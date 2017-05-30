module Data.Machine.Plan
  ( PlanT(..)
  , Plan
  , unPlanT
  , runPlanT
  , runPlan
  , encased
  , yield
  , maybeYield
  , await
  , awaits
  , stop

  , Step
  , AwaitX
  , mkAwait
  , unAwait
  ) where

import Prelude

import Control.Alt (class Alt)
import Control.Alternative (class Alternative)
import Control.Monad.Aff.Class (class MonadAff, liftAff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Plus (class Plus, empty)
import Control.MonadPlus (class MonadZero, class MonadPlus)
import Control.Monad.Trans.Class (class MonadTrans, lift)

import Data.Exists (Exists, mkExists, runExists)
import Data.Identity (Identity)
import Data.Maybe (Maybe(..))
import Data.Lazy (Lazy, defer)
import Data.Newtype (wrap, unwrap)


newtype PlanT k o m r = PlanT (forall b. (r -> Step k o m b) -> Step k o m b)

type Plan k o a = forall m. PlanT k o m a

data Step k o m r
  = Stop
  | Done r
  | Yield o (Lazy (Step k o m r))
  | StepM (m (Step k o m r))
  | Await (Exists (AwaitX k o m r))

data AwaitX k o m r t = AwaitX (t -> Step k o m r) (k t) (Lazy (Step k o m r))

unAwait :: forall k o m r a. (forall t. (t -> Step k o m r) -> k t -> Lazy (Step k o m r) -> a) -> Exists (AwaitX k o m r) -> a
unAwait f = runExists \(AwaitX g kg fg) -> f g kg fg

mkAwait :: forall k o m r t. (t -> Step k o m r) -> k t -> Lazy (Step k o m r) -> Step k o m r
mkAwait f g = Await <<< mkExists <<< AwaitX f g

unPlanT
  :: forall k o m r
   . PlanT k o m r
  -> (forall b. (r -> Step k o m b) -> Step k o m b)
unPlanT (PlanT k) = k

yield :: forall k o. o -> Plan k o Unit
yield o = PlanT \k -> Yield o (defer \_ -> k unit)

maybeYield :: forall k o. Maybe o -> Plan k o Unit
maybeYield = case _ of
  Nothing -> stop
  Just a  -> yield a

await :: forall k o i. Category k => Plan (k i) o i
await = PlanT \k -> mkAwait k id (defer \_ -> Stop)

awaits :: forall k o i. k i -> Plan k o i
awaits h = PlanT \k -> mkAwait k h (defer \_ -> Stop)

stop :: forall k o a. Plan k o a
stop = PlanT \_ -> Stop

encased :: forall k o m r. Functor m => Step k o m r -> PlanT k o m r
encased s = PlanT \k ->
  let
    go = case _ of
      Stop      -> Stop
      Done r    -> k r
      Yield o l -> Yield o (map go l)
      StepM ms  -> StepM (map go ms)
      Await aw  -> aw # unAwait \ff kg fg -> mkAwait (go <<< ff) kg (map go fg)
  in go s

runPlanT
  :: forall k o m a r. Bind m
  => PlanT k o m a
  -> (a -> m r)
  -> (o -> Lazy (m r) -> m r)
  -> (forall z. (z -> m r) -> k z -> Lazy (m r) -> m r)
  -> m r
  -> m r
runPlanT (PlanT k) done yi emit fail = go (k Done)
  where
  go :: Step k o m a -> m r
  go = case _ of
    Done a     -> done a
    Stop       -> fail
    Yield o kk -> yi o (map go kk)
    StepM m    -> m >>= go
    Await de   -> de # unAwait \fg kg dg -> emit (go <<< fg) kg (map go dg)

runPlan
  :: forall k o a r
   . PlanT k o Identity a
  -> (a -> r)
  -> (o -> Lazy r -> r)
  -> (forall z. (z -> r) -> k z -> Lazy r -> r)
  -> r
  -> r
runPlan m kp ke kr kf = unwrap $ runPlanT m
  (wrap <<< kp)
  (\o r -> wrap (ke o (map unwrap r)))
  (\f k r -> wrap (kr (unwrap <<< f) k (map unwrap r)))
  (wrap kf)

instance functorPlanT :: Functor (PlanT k o m) where
  map f (PlanT k) = PlanT (\m -> k (m <<< f))

instance applyPlanT :: Apply (PlanT k o m) where
  apply (PlanT f) (PlanT g) = PlanT (\bfr -> f (\ab -> g (bfr <<< ab)))

instance applicativePlanT :: Applicative (PlanT k o m) where
  pure a = PlanT \k -> k a

instance bindPlanT :: Bind (PlanT k o m) where
  bind (PlanT m) k = PlanT (\c -> m (\a -> case k a of PlanT ff -> ff c))

instance monadPlanT :: Monad (PlanT k o m)

instance altPlanT :: Functor m => Alt (PlanT k o m) where
  alt (PlanT m) (PlanT n) = PlanT \k ->
    let
      go Stop       = n k
      go (StepM ms) = StepM (map go ms)
      go r          = r
    in go (m k)

instance plusPlanT :: Functor m => Plus (PlanT k o m) where
  empty = PlanT \_ -> Stop

instance alternativePlanT :: Functor m => Alternative (PlanT k o m)

instance monadZeroPlanT :: Functor m => MonadZero (PlanT k o m)

instance monadPlusPlanT :: Functor m => MonadPlus (PlanT k o m)

instance monadTransPlanT :: MonadTrans (PlanT k o) where
  lift m = PlanT \k -> StepM (k <$> m)

instance monadEffPlanT :: MonadEff eff m => MonadEff eff (PlanT k o m) where
  liftEff = lift <<< liftEff

instance monadAffPlanT :: MonadAff eff m => MonadAff eff (PlanT k o m) where
  liftAff = lift <<< liftAff

instance functorStep :: Functor m => Functor (Step k o m) where
  map f = go
    where
    go = case _ of
      Stop      -> Stop
      Done r    -> Done (f r)
      Yield o l -> Yield o (map go l)
      StepM ms  -> StepM (map go ms)
      Await aw  -> aw # unAwait \ff kg fg -> mkAwait (go <<< ff) kg (map go fg)
