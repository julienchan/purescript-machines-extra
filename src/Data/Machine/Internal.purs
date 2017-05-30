module Data.Machine.Internal where

import Prelude

import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.Rec.Class (Step(..), tailRecM, tailRecM2) as Rec

import Data.Exists (Exists, mkExists, runExists)
import Data.Lazy (Lazy, defer, force)
import Data.List (List(Nil), (:), reverse)
import Data.Monoid (class Monoid)
import Data.Newtype (class Newtype, unwrap)
import Data.Machine.Plan (PlanT, runPlanT)
import Data.Identity (Identity)

data Step k o r
  = Stop
  | Yield o (Lazy r)
  | Await (Exists (AwaitX k o r))

data AwaitX k o r t = AwaitX (t -> r) (k t) (Lazy r)

instance functorStep :: Functor (Step k o) where
  map _ Stop            = Stop
  map f (Yield o r)     = Yield o (map f r)
  map f (Await x)       = x # unAwait \g kg fg -> mkAwait (f <<< g) kg (map f fg)

unAwait :: forall k o r a. (forall t. (t -> r) -> k t -> Lazy r -> a) -> Exists (AwaitX k o r) -> a
unAwait f = runExists \(AwaitX g kg fg) -> f g kg fg

mkAwait :: forall k o r t. (t -> r) -> k t -> Lazy r -> Step k o r
mkAwait f g = Await <<< mkExists <<< AwaitX f g

encased :: forall m k o. Applicative m => Step k o (MachineT m k o) -> MachineT m k o
encased b = MachineT (pure b)

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
    f' (Yield o xs)    = Yield (f o) (map (map f) xs)
    f' (Await x)       = x # unAwait \k kir e -> mkAwait (map f <<< k) kir (map (map f) e)
    f' Stop            = Stop

instance semigroupMachineT :: Monad m => Semigroup (MachineT m k o) where
  append a b = stepMachine a $ \step -> case step of
    Yield o a' -> encased (Yield o (defer \_ -> append (force a') b))
    Await ex   -> ex # unAwait \k kir e -> encased (mkAwait (\x -> k x <> b) kir (defer \_ -> force e <> b))
    Stop       -> b

instance monoidMachineT :: Monad m => Monoid (MachineT m k o) where
  mempty = stopped

runRecT_ :: forall m k b. MonadRec m => MachineT m k b -> m Unit
runRecT_ = Rec.tailRecM go
  where
  go (MachineT m) = m >>= \v -> case v of
    Stop      -> pure $ Rec.Done unit
    Yield _ r -> pure $ Rec.Loop (force r)
    Await x   -> x # unAwait \_ _ e -> pure $ Rec.Loop (force e)

runT_ :: forall m k b. Monad m => MachineT m k b -> m Unit
runT_ = go
  where
  go (MachineT m) = m >>= \v -> case v of
    Stop      -> pure unit
    Yield _ r -> go (force r)
    Await x   -> x # unAwait \_ _ e -> go (force e)

runRecT :: forall m k b. MonadRec m => MachineT m k b -> m (List b)
runRecT = Rec.tailRecM2 go Nil
  where
  go x (MachineT m) = m >>= \v -> case v of
    Stop        -> pure $ Rec.Done (reverse x)
    Yield o k   -> pure $ Rec.Loop {a: (o:x), b: force k }
    Await b     -> b # unAwait \_ _ e -> pure (Rec.Loop {a: x, b: force e})

runRec :: forall k b. MachineT Identity k b -> List b
runRec = unwrap <<< runRecT

stopped :: forall k b. Machine k b
stopped = encased Stop

fit :: forall k k' o m. Functor m => (k ~> k') -> MachineT m k o -> MachineT m k' o
fit f (MachineT m) = MachineT (f' <$> m)
  where
  f' (Yield o k)     = Yield o (defer \_ -> fit f (force k))
  f' Stop            = Stop
  f' (Await b)       = b # unAwait \g kir h -> mkAwait (fit f <<< g) (f kir) (map (fit f) h)

fitM :: forall k o m n. Functor m => Functor n => (m ~> n) -> MachineT m k o -> MachineT n k o
fitM f (MachineT m) = MachineT (f (map aux m))
  where
  aux Stop = Stop
  aux (Yield o k) = Yield o (map (fitM f) k)
  aux (Await o)   = o # unAwait \g kg gg -> mkAwait (fitM f <<< g) kg (map (fitM f) gg)

construct :: forall k o m a. Monad m => PlanT k o m a -> MachineT m k o
construct m = MachineT (runPlanT m
  (const (pure Stop))
  (\o k -> pure (Yield o (defer \_ -> MachineT $ force k)))
  (\f k g -> pure (mkAwait (MachineT <<< f) k (defer \_ -> MachineT $ force g)))
  (pure Stop))

repeatedly :: forall k o m a. MonadRec m => PlanT k o m a -> MachineT m k o
repeatedly = go
  where
  go m = MachineT $ runPlanT m
    (\_ -> unwrap (go m))
    (\o k -> pure (Yield o (defer \_ -> MachineT $ force k)))
    (\f k g -> pure (mkAwait (MachineT <<< f) k (defer \_ -> MachineT $ force g)))
    (pure Stop)

unfoldPlan :: forall k o m s. Monad m => s -> (s -> PlanT k o m s) -> MachineT m k o
unfoldPlan s0 sp = r s0
  where
  r s = MachineT $ runPlanT (sp s)
    (\sx -> unwrap $ r sx)
    (\o k -> pure (Yield o (defer \_ -> MachineT $ force k)))
    (\f k g -> pure (mkAwait (MachineT <<< f) k (defer \_ -> MachineT $ force g)))
    (pure Stop)

before :: forall k o m a. Monad m => MachineT m k o -> PlanT k o m a -> MachineT m k o
before (MachineT n) m = MachineT $ runPlanT m
  (const n)
  (\o k -> pure (Yield o (defer \_ -> MachineT $ force k)))
  (\f k g -> pure (mkAwait (MachineT <<< f) k (defer \_ -> MachineT $ force g)))
  (pure Stop)

preplan :: forall k o m. Monad m => PlanT k o m (MachineT m k o) -> MachineT m k o
preplan m = MachineT $ runPlanT m
  unwrap
  (\o k -> pure (Yield o (defer \_ -> MachineT $ force k)))
  (\f k g -> pure (mkAwait (MachineT <<< f) k (defer \_ -> MachineT $ force g)))
  (pure Stop)

pass :: forall k o. k o -> Machine k o
pass k = go
  where
  go = encased (mkAwait (\t -> encased (Yield t (defer \_ -> go))) k (defer \_ -> stopped))

starve :: forall m k k0 b. Monad m => MachineT m k0 b -> MachineT m k b -> MachineT m k b
starve m cont = MachineT $ unwrap m >>= \v -> case v of
  Stop      -> unwrap cont -- Continue with cont instead of stopping
  Yield o r -> pure $ Yield o (defer \_ -> starve (force r) cont)
  Await b   -> b # unAwait \_ _ r -> unwrap (starve (force r) cont)
