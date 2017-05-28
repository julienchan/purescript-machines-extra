module Data.Machine.Types where

import Prelude

import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.Rec.Class (Step(..), tailRecM, tailRecM2) as Rec

import Data.Exists (Exists, mkExists, runExists)
import Data.List (List(Nil), (:), reverse)
import Data.Monoid (class Monoid)
import Data.Newtype (class Newtype, unwrap)
import Data.Machine.Plan (PlanT, runPlanT)
import Data.Identity (Identity)

data Step k o r
  = Stop
  | Yield o r
  | Await (Exists (Await' k o r))

data Await' k o r t = Await' (t -> r) (k t) r

instance functorStep :: Functor (Step k o) where
  map _ Stop            = Stop
  map f (Yield o r)     = Yield o (f r)
  map f (Await x)       = x # unAwait' \g kg fg -> mkAwait' (f <<< g) kg (f fg)

unAwait' :: forall k o r a. (forall t. (t -> r) -> k t -> r -> a) -> Exists (Await' k o r) -> a
unAwait' f = runExists \(Await' g kg fg) -> f g kg fg

mkAwait' :: forall k o r t. (t -> r) -> k t -> r -> Step k o r
mkAwait' f g = Await <<< mkExists <<< Await' f g

encased :: forall m k o. Applicative m => Step k o (MachineT m k o) -> MachineT m k o
encased = MachineT <<< pure

stepMachine
  :: forall m k k' o o'
   . Bind m
  => MachineT m k o
  -> (Step k o (MachineT m k o) -> MachineT m k' o')
  -> MachineT m k' o'
stepMachine m f = MachineT (unwrap <<< f =<< unwrap m)

-- | A 'MachineT' reads from a number of inputs and may yield results before stopping
-- | with monadic side-effects.
newtype MachineT m k o = MachineT (m (Step k o (MachineT m k o)))

-- | A 'Machine' reads from a number of inputs and may yield results before stopping.
--
-- A 'Machine' can be used as a @'MachineT' m@ for any @'Monad' m@.
type Machine k o = forall m. Monad m => MachineT m k o

derive instance newtypeMachineT :: Newtype (MachineT m k o) _

instance functorMachineT :: Functor m => Functor (MachineT m k) where
  map f (MachineT m) = MachineT (f' <$> m)
    where
    f' (Yield o xs)    = Yield (f o) (f <$> xs)
    f' (Await x)       = x # unAwait' \k kir e -> mkAwait' (map f <<< k) kir (f <$> e)
    f' Stop            = Stop

instance semigroupMachineT :: Monad m => Semigroup (MachineT m k o) where
  append a b = stepMachine a $ \step -> case step of
    Yield o a' -> encased (Yield o (append a' b))
    Await ex   -> ex # unAwait' \k kir e -> encased (mkAwait' (\x -> k x <> b) kir (e <> b))
    Stop       -> b

instance monoidMachineT :: Monad m => Monoid (MachineT m k o) where
  mempty = stopped

runT_ :: forall m k b. MonadRec m => MachineT m k b -> m Unit
runT_ = Rec.tailRecM go
  where
  go (MachineT m) = m <#> \v -> case v of
    Stop      -> Rec.Done unit
    Yield _ r -> Rec.Loop r
    Await x   -> x # unAwait' \_ _ e -> Rec.Loop e

runT :: forall m k b. MonadRec m => MachineT m k b -> m (List b)
runT = Rec.tailRecM2 go Nil
  where
  go x (MachineT m) = m >>= \v -> case v of
    Stop        -> pure $ Rec.Done (reverse x)
    Yield o k   -> pure $ Rec.Loop {a: (o:x), b: k }
    Await b     -> b # unAwait' \_ _ e -> pure (Rec.Loop {a: x, b: e})

run :: forall k b. MachineT Identity k b -> List b
run = unwrap <<< runT

stopped :: forall k b. Machine k b
stopped = encased Stop

fit :: forall k k' o m. Monad m => (k ~> k') -> MachineT m k o -> MachineT m k' o
fit f (MachineT m) = MachineT (f' <$> m)
  where
  f' (Yield o k)     = Yield o (fit f k)
  f' Stop            = Stop
  f' (Await b)       = b # unAwait' \g kir h -> mkAwait' (fit f <<< g) (f kir) (fit f h)

construct :: forall k o m a. Monad m => PlanT k o m a -> MachineT m k o
construct m = MachineT (runPlanT m
  (const (pure Stop))
  (\o k -> pure (Yield o (MachineT k)))
  (\f k g -> pure (mkAwait' (MachineT <<< f) k (MachineT g)))
  (pure Stop))

unfoldPlan :: forall k o m s. Monad m => s -> (s -> PlanT k o m s) -> MachineT m k o
unfoldPlan s0 sp = r s0
  where
  r s = MachineT $ runPlanT (sp s)
    (\sx -> unwrap $ r sx)
    (\o k -> pure (Yield o (MachineT k)))
    (\f k g -> pure (mkAwait' (MachineT <<< f) k (MachineT g)))
    (pure Stop)
