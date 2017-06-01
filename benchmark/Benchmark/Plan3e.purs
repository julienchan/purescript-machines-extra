module Benchmark.Machine.Plan where

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


data PlanT k o m r
  = Stop
  | Done r
  | Yield o (Lazy (PlanT k o m r))
  | StepM (m (PlanT k o m r))
  | Await (Exists (AwaitX k o m r))

type Plan k o a = forall m. PlanT k o m a

data AwaitX k o m r t = AwaitX (t -> PlanT k o m r) (k t) (Lazy (PlanT k o m r))

unAwait :: forall k o m r a. (forall t. (t -> PlanT k o m r) -> k t -> Lazy (PlanT k o m r) -> a) -> Exists (AwaitX k o m r) -> a
unAwait f = runExists \(AwaitX g kg fg) -> f g kg fg

mkAwait :: forall k o m r t. (t -> PlanT k o m r) -> k t -> Lazy (PlanT k o m r) -> PlanT k o m r
mkAwait f g = Await <<< mkExists <<< AwaitX f g

yield :: forall k o. o -> Plan k o Unit
yield o = Yield o (defer \_ -> Done unit)

maybeYield :: forall k o. Maybe o -> Plan k o Unit
maybeYield = case _ of
  Nothing -> stop
  Just a  -> yield a

await :: forall k o i. Category k => Plan (k i) o i
await = mkAwait Done id (defer \_ -> Stop)

awaits :: forall k o i. k i -> Plan k o i
awaits h = mkAwait Done h (defer \_ -> Stop)

stop :: forall k o a. Plan k o a
stop = Stop

runPlanT
  :: forall k o m a r. Bind m
  => PlanT k o m a
  -> (a -> m r)
  -> (o -> Lazy (m r) -> m r)
  -> (forall z. (z -> m r) -> k z -> Lazy (m r) -> m r)
  -> m r
  -> m r
runPlanT k done yi emit fail = go k
  where
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

instance functorPlanT :: Functor m => Functor (PlanT k o m) where
  map f = go
    where
    go = case _ of
      Done r -> Done (f r)
      Stop   -> Stop
      Yield o k -> Yield o (map go k)
      StepM mp  -> StepM (map go mp)
      Await ex  -> ex # unAwait \k fg h -> mkAwait (go <<< k) fg (map go h)

instance applyPlanT :: Functor m => Apply (PlanT k o m) where
  apply ff fg = go ff
    where
    go = case _ of
      Done f    -> f <$> fg
      Stop      -> Stop
      Yield o k -> Yield o (map go k)
      StepM mp  -> StepM (map go mp)
      Await ex  -> ex # unAwait \k fg h -> mkAwait (go <<< k) fg (map go h)

instance applicativePlanT :: Functor m => Applicative (PlanT k o m) where
  pure = Done

instance bindPlanT :: Functor m => Bind (PlanT k o m) where
  bind m k = go m
    where
    go = case _ of
      Done a    -> k a
      Stop      -> Stop
      Yield o k -> Yield o (map go k)
      StepM mp  -> StepM (map go mp)
      Await ex  -> ex # unAwait \k fg h -> mkAwait (go <<< k) fg (map go h)

instance monadPlanT :: Functor m => Monad (PlanT k o m)

instance altPlanT :: Functor m => Alt (PlanT k o m) where
  alt lm ln = go lm
    where
    go = case _ of
      Done a    -> Done a
      Stop      -> ln
      Yield o k -> Yield o (map go k)
      StepM mp  -> StepM (map go mp)
      Await ex  -> ex # unAwait \k fg h -> mkAwait (go <<< k) fg (map go h)

instance plusPlanT :: Functor m => Plus (PlanT k o m) where
  empty = Stop

instance alternativePlanT :: Functor m => Alternative (PlanT k o m)

instance monadZeroPlanT :: Functor m => MonadZero (PlanT k o m)

instance monadPlusPlanT :: Functor m => MonadPlus (PlanT k o m)

instance monadTransPlanT :: MonadTrans (PlanT k o) where
  lift m = StepM (Done <$> m)

instance monadEffPlanT :: MonadEff eff m => MonadEff eff (PlanT k o m) where
  liftEff = lift <<< liftEff

instance monadAffPlanT :: MonadAff eff m => MonadAff eff (PlanT k o m) where
  liftAff = lift <<< liftAff
