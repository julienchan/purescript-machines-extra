module Data.Machine.Plan where

import Prelude

import Control.Alt (class Alt)
import Control.Alternative (class Alternative)
import Control.Monad.Aff.Class (class MonadAff, liftAff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Plus (class Plus, empty)
import Control.MonadPlus (class MonadZero, class MonadPlus)
import Control.Monad.Trans.Class (class MonadTrans)

import Data.Identity (Identity)
import Data.Maybe (Maybe(..))
import Data.Newtype (wrap, unwrap)

newtype PlanT k o m a = PlanT
  (forall r.
    (a -> m r) ->                                     -- Done a
    (o -> m r -> m r) ->                              -- Yield o (Plan k o a)
    (forall z. (z -> m r) -> k z -> m r -> m r) ->    -- forall z. Await (z -> Plan k o a) (k z) (Plan k o a)
    m r ->                                            -- Fail
    m r
  )

type Plan k o a = forall m. PlanT k o m a

runPlanT
  :: forall k o m a
   . PlanT k o m a
  -> (forall r.
       (a -> m r) ->
       (o -> m r -> m r) ->
       (forall z. (z -> m r) -> k z -> m r -> m r) ->
        m r ->
        m r)
runPlanT (PlanT k) = k

runPlan
  :: forall k o a r
   . PlanT k o Identity a
  -> (a -> r)
  -> (o -> r -> r)
  -> (forall z. (z -> r) -> k z -> r -> r)
  -> r
  -> r
runPlan m kp ke kr kf = unwrap $ runPlanT m
  (wrap <<< kp)
  (\o r -> wrap (ke o (unwrap r)))
  (\f k r -> wrap (kr (unwrap <<< f) k (unwrap r)))
  (wrap kf)

yield :: forall k o. o -> Plan k o Unit
yield o = PlanT (\kp ke _ _ -> ke o (kp unit))

maybeYield :: forall k o. Maybe o -> Plan k o Unit
maybeYield = case _ of
  Nothing -> stop
  Just a  -> yield a

await :: forall k o i. Category k => Plan (k i) o i
await = PlanT (\kp _ kr kf -> kr kp id kf)

awaits :: forall k o i. k i -> Plan k o i
awaits h = PlanT (\kp _ kr -> kr kp h)

stop :: forall k o a. Plan k o a
stop = empty

instance functorPlanT :: Functor (PlanT k o m) where
  map f (PlanT m) = PlanT (\k -> m (k <<< f))

instance applyPlanT :: Apply (PlanT k o m) where
  apply (PlanT m) (PlanT n) = PlanT (\kp ke kr kf -> m (\f -> n (\a -> kp (f a)) ke kr kf) ke kr kf)

instance applicativePlanT :: Applicative (PlanT k o m) where
  pure a = PlanT \k _ _ _ -> k a

instance bindPlanT :: Bind (PlanT k o m) where
  bind (PlanT m) f = PlanT (\kp ke kr kf -> m (\a -> runPlanT (f a) kp ke kr kf) ke kr kf)

instance monadPlanT :: Monad (PlanT k o m)

instance altPlanT :: Alt (PlanT k o m) where
  alt (PlanT m) (PlanT n) = PlanT (\kp ke kr kf -> m kp ke kr (n kp ke kr kf))

instance plusPlanT :: Plus (PlanT k o m) where
  empty = PlanT (\_ _ _ kf -> kf)

instance alternativePlanT :: Alternative (PlanT k o m)

instance monadZeroPlanT :: MonadZero (PlanT k o m)

instance monadPlusPlanT :: MonadPlus (PlanT k o m)

instance monadTransPlanT :: MonadTrans (PlanT k o) where
  lift m = PlanT (\kp _ _ _ -> m >>= kp)

instance monadEffPlanT :: MonadEff eff m => MonadEff eff (PlanT k o m) where
  liftEff m = PlanT (\kp _ _ _ -> liftEff m >>= kp)

instance monadAffPlanT :: MonadAff eff m => MonadAff eff (PlanT k o m) where
  liftAff m = PlanT (\kp _ _ _ -> liftAff m >>= kp)
