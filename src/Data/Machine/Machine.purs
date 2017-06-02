module Data.Machine.Machine where

import Prelude

import Control.MonadPlus (empty)

import Data.Lazy (Lazy, defer)
import Data.Exists (Exists, mkExists, runExists)

import Data.Machine.Internal.FreePlus (FreePlus, suspendF, hoistFree)

data MachineF m k o a
  = Await (Exists (AwaitX k o a)) -- forall t. Await (t -> a) (k t) a
  | Yield o (Lazy a)
  | Lift (m a)

instance functorMachineF :: Functor m => Functor (MachineF m k o) where
  map f = go
    where
    go = case _ of
      Yield o a -> Yield o (f <$> a)
      Await aw  -> aw # unAwait \k g s -> mkAwait (f <<< k) g (f <$> s)
      Lift ma   -> Lift (f <$> ma)

data AwaitX k o a t = AwaitX (t -> a) (k t) (Lazy a)

-- | A 'MachineT' reads from a number of inputs and may yield results before stopping
-- | with monadic side-effects.
type MachineT m k o a = FreePlus (MachineF m k o) a

-- | A 'Machine' reads from a number of inputs and may yield results before stopping.
-- |
-- | A 'Machine' can be used as a @'MachineT' m@ for any @'Monad' m@.
type Machine k o a = forall m. Monad m => MachineT m k o a

unAwait
  :: forall k o a r. (forall t. (t -> a) -> k t -> Lazy a -> r)
  -> Exists (AwaitX k o a)
  -> r
unAwait k = runExists \(AwaitX t h a) -> k t h a

mkAwait
  :: forall m k o a t
   . (t -> a)
  -> k t
  -> Lazy a
  -> MachineF m k o a
mkAwait t k = Await <<< mkExists <<< AwaitX t k

-- | Stop the Machine
stop :: forall k o a. Machine k o a
stop = empty

-- | Emit an output value
yield :: forall k o. o -> Machine k o Unit
yield o = suspendF (Yield o (defer \_ -> pure unit))

-- | Wait for input.
await :: forall k o i. Category k => Machine (k i) o i
await = suspendF (mkAwait pure id (defer \_ -> stop))

-- | Wait for a particular input.
awaits :: forall k o i. k i -> Machine k o i
awaits ki = suspendF (mkAwait pure ki (defer \_ -> stop))

-- | Pack a 'Step' of a 'Machine' into a 'Machine'.
encased :: forall m k o a. MachineF m k o (MachineT m k o a) -> MachineT m k o a
encased = suspendF

-- | Connect different kinds of machines.
fit :: forall m k l o a. Functor m => (k ~> l) -> MachineT m k o a -> MachineT m l o a
fit k = hoistFree go
  where
  go :: MachineF m k o ~> MachineF m l o
  go (Await xx)  = xx # unAwait \f t s -> mkAwait f (k t) s
  go (Yield o a) = Yield o a
  go (Lift m)    = Lift m

-- | Connect machine transformers over different monads using a monad morphism.
fitM
  :: forall m n k o a. Functor m => Functor n
  => (m ~> n) -> MachineT m k o a -> MachineT n k o a
fitM k = hoistFree go
  where
  go :: MachineF m k o ~> MachineF n k o
  go (Lift m)    = Lift (k m)
  go (Yield o a) = Yield o a
  go (Await xx)  = Await xx