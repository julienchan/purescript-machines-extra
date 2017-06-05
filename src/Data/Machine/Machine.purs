module Data.Machine.Machine where

import Prelude

import Control.Monad.Aff.Class (class MonadAff, liftAff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Alt (class Alt)
import Control.Plus (class Plus, empty)
import Control.Alternative (class Alternative)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Control.Monad.Trans.Class (class MonadTrans)
import Control.MonadPlus (class MonadZero, class MonadPlus)

import Data.Newtype (class Newtype)
import Data.Exists (Exists, mkExists, runExists)

import Data.Machine.Internal.FreePlus (FreePlus, wrapF, hoistFree, liftF, runFreeM)

data MachineF k o m a
  = Await (Exists (AwaitX k o a)) -- forall t. Await (t -> a) (k t) a
  | Yield o a
  | Lift (m a)

instance functorMachineF :: Functor m => Functor (MachineF k o m) where
  map f = go
    where
    go = case _ of
      Yield o a -> Yield o (f a)
      Await aw  -> aw # unAwait \k g s -> mkAwait (f <<< k) g (f s)
      Lift ma   -> Lift (f <$> ma)

data AwaitX k o a t = AwaitX (t -> a) (k t) a

-- | A 'MachineT' reads from a number of inputs and may yield results before stopping
-- | with monadic side-effects.
newtype MachineT k o m a = MachineT (FreePlus (MachineF k o m) a)

-- | A 'Machine' reads from a number of inputs and may yield results before stopping.
-- |
-- | A 'Machine' can be used as a @'MachineT' m@ for any @'Monad' m@.
type Machine k o a = forall m. Monad m => MachineT k o m a

unAwait
  :: forall k o a r. (forall t. (t -> a) -> k t -> a -> r)
  -> Exists (AwaitX k o a)
  -> r
unAwait k = runExists \(AwaitX t h a) -> k t h a

mkAwait
  :: forall m k o a t
   . (t -> a)
  -> k t
  -> a
  -> MachineF k o m a
mkAwait t k = Await <<< mkExists <<< AwaitX t k

-- | Stop the Machine
stopped :: forall k o a. Machine k o a
stopped = MachineT empty

-- | Emit an output value
yield :: forall k o. o -> Machine k o Unit
yield o = MachineT (wrapF (Yield o (pure unit)))

-- | Wait for input.
await :: forall k o i. Category k => Machine (k i) o i
await = MachineT (wrapF (mkAwait pure id empty))

-- | Wait for a particular input.
awaits :: forall k o i. k i -> Machine k o i
awaits ki = MachineT (wrapF (mkAwait pure ki empty))

-- | Pack a 'Step' of a 'Machine' into a 'Machine'.
encased :: forall m k o a. MachineF k o m (FreePlus (MachineF k o m) a) -> MachineT k o m a
encased = MachineT <<< wrapF

-- | Connect different kinds of machines.
fit :: forall m k l o a. Functor m => (k ~> l) -> MachineT k o m a -> MachineT l o m a
fit k (MachineT fre) = MachineT (hoistFree go fre)
  where
  go :: MachineF k o m ~> MachineF l o m
  go (Await xx)  = xx # unAwait \f t s -> mkAwait f (k t) s
  go (Yield o a) = Yield o a
  go (Lift m)    = Lift m

runRecT_ :: forall k o m a. MonadRec m => MonadPlus m => MachineT k o m a -> m a
runRecT_ (MachineT fa) = runFreeM go fa
  where
  go = case _ of
    Lift ma   -> ma
    Yield _ o -> pure o
    Await a   -> a # unAwait \_ _ e -> pure e

-- | Connect machine transformers over different monads using a monad morphism.
fitM
  :: forall m n k o a. Functor m => Functor n
  => (m ~> n) -> MachineT k o m a -> MachineT k o n a
fitM k (MachineT fre) = MachineT (hoistFree go fre)
  where
  go :: MachineF k o m ~> MachineF k o n
  go (Lift m)    = Lift (k m)
  go (Yield o a) = Yield o a
  go (Await xx)  = Await xx

derive instance newtypeMachineT :: Newtype (MachineT k o m a) _
derive newtype instance functorMachineT :: Functor (MachineT k o m)
derive newtype instance applyMachineT :: Apply (MachineT k o m)
derive newtype instance applicativeMachineT :: Applicative (MachineT k o m)
derive newtype instance bindMachineT :: Bind (MachineT k o m)
derive newtype instance monadMachineT :: Monad (MachineT k o m)
derive newtype instance altMachineT :: Alt (MachineT k o m)
derive newtype instance plusMachineT :: Plus (MachineT k o m)
derive newtype instance alternativeMachineT :: Alternative (MachineT k o m)
derive newtype instance monadZeroMachineT :: MonadZero (MachineT k o m)
derive newtype instance monadPlusMachineT :: MonadPlus (MachineT k o m)

instance monadEffMachineT :: MonadEff eff m => MonadEff eff (MachineT k o m) where
  liftEff eff = MachineT $ liftF $ Lift $ liftEff eff

instance monadAffMachineT :: MonadAff eff m => MonadAff eff (MachineT k o m) where
  liftAff aff = MachineT $ liftF $ Lift $ liftAff aff

instance monadTransMachineT:: MonadTrans (MachineT k o) where
  lift m = MachineT $ liftF $ Lift m

instance monadRecMachineT :: MonadRec (MachineT k o m) where
  tailRecM k a = k a >>= case _ of
    Loop b -> tailRecM k b
    Done r -> pure r
