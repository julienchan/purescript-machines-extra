module Data.Machine.Pipe where

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM) as Rec

import Data.Machine.Plan (PlanT, awaits)
import Data.Machine.Machine (MachineT(..), Step(..), construct, unAwait, mkAwait)
import Data.Newtype (unwrap)
import Data.Leibniz (type (~), coerceSymm)
import Data.List (List(Nil), (:))

data Exchange a' a b' b c
  = Request a' (c ~ a)
  | Respond b  (c ~ b')

type Duplex a' a b' b m c = MachineT m (Exchange a' a b' b) c

-- | 'Effect's neither 'request' nor 'respond'
type Effect m r = Duplex Void Unit Unit Void m r

-- | @Client a' a@ sends requests of type @a'@ and receives responses of
--   type @a@. 'Client's only 'request' and never 'respond'.
type Client a' a m r = Duplex a' a Unit Void m r

-- | @Server b' b@ receives requests of type @b'@ and sends responses of type
--   @b@. 'Server's only 'respond' and never 'request'.
type Server b' b m r = Duplex Void Unit b' b m r

-- | Like 'Effect', but with a polymorphic type
type Effect' m r = forall x' x y' y . Duplex x' x y' y m r

-- | Like 'Server', but with a polymorphic type
type Server' b' b m r = forall x' x . Duplex x' x b' b m r

-- | Like 'Client', but with a polymorphic type
type Client' a' a m r = forall y' y . Duplex a' a y' y m r

request :: forall a' a y' y o m. a' -> PlanT (Exchange a' a y' y) o m a
request a = awaits (Request a id)

-- | Send a value of type a downstream and block waiting for a reply of type a'
--  'respond' is the identity of the respond category.
respond :: forall a' a x' x o m. a -> PlanT (Exchange x' x a' a) o m a'
respond a = awaits (Respond a id)

-- | Forward responses followed by requests.
--   'push' is the identity of the push category.
push :: forall a a' m r. Monad m => a -> Duplex a' a a' a m r
push = construct <<< go
  where
    go = respond >=> request >=> \x -> go x

-- | Forward requests followed by responses.
--   'pull' is the identity of the pull category.
pull :: forall a' a m r. Monad m => a' -> Duplex a' a a' a m r
pull = construct <<< go
  where
    go = request >=> respond >=> \x -> go x

composePush
  :: forall m _a a' a b' b c' c r
   . Monad m
  => (_a -> Duplex a' a b' b m r)
  -> (b -> Duplex b' b c' c m r)
  -> _a -> Duplex a' a c' c m r
composePush fa fb a = fa a >>~ fb

infixl 8 composePush as >~>

chainPush
  :: forall a' a b b' c' c m r
   . Monad m
  => Duplex a' a b' b m r
  -> (b -> Duplex b' b c' c m r)
  -> Duplex a' a c' c m r
chainPush pm fb = MachineT $ unwrap pm >>= \p ->
  case p of
    Stop       -> pure Stop
    Yield r n  -> pure $ Yield r (n >>~ fb)
    Await be   -> be # unAwait \k exc ff -> case exc of
      Request a' pf -> pure $ mkAwait (\a -> k (coerceSymm pf a) >>~ fb) (Request a' id) (ff >>~ fb)
      Respond b pf -> unwrap (k <<< coerceSymm pf +>> fb b)

infixl 7 chainPush as >>~

composePull
  :: forall a' a b' b c' c _c' m r
  .  Monad m
  => (b' -> Duplex a' a b' b m r)
  -> (_c' -> Duplex b' b c' c m r)
  -> _c' -> Duplex a' a c' c m r
composePull fb' fc' c' = fb' +>> fc' c'

infixl 7 composePull as >+>

chainPull
  :: forall a' a b b' c c' m r
   . Monad m
  => (b' -> Duplex a' a b' b m r)
  -> Duplex b' b c' c m r
  -> Duplex a' a c' c m r
chainPull fb' pm = MachineT $ unwrap pm >>= \p ->
  case p of
    Stop                   -> pure Stop
    Yield r n              -> pure $ Yield r (fb' +>> n)
    Await be   -> be # unAwait \k exc ff -> case exc of
      Request b' pf -> unwrap (fb' b' >>~ coerceSymm pf >>> k)
      Respond c  pf -> pure $ mkAwait (\c' -> fb' +>> k (coerceSymm pf c')) (Respond c id) (fb' +>> ff)

infixl 6 chainPull as +>>

-- | It is impossible for an `Exchange` to hold a `Void` value.
absurdExchange :: forall a b t c. Exchange Void a b Void t -> c
absurdExchange (Request z _) = absurd z
absurdExchange (Respond z _) = absurd z

-- | Run a self-contained 'Effect', converting it back to the base monad.
runEffect :: forall m o. Monad m => Effect m o -> m (List o)
runEffect (MachineT m) = m >>= \v ->
  case v of
    Stop      -> pure Nil
    Yield o n -> map ((:)o) (runEffect n)
    Await ye   -> ye # unAwait' \_ y _ -> absurdExchange y

runEffect' :: forall m o. Monad m => Effect m o -> m Unit
runEffect' (MachineT m) = m >>= \v ->
  case v of
    Stop      -> pure unit
    Yield _ n -> runEffect' n
    Await be  -> be # unAwait \_ y _ -> absurdExchange y

runEffectRec :: forall m o. Rec.MonadRec m => Effect m o -> m Unit
runEffectRec = Rec.tailRecM go
  where
  go :: Effect m o -> m (Rec.Step (Effect m o) Unit)
  go (MachineT m) = m >>= \v -> case v of
    Stop -> pure (Rec.Done unit)
    Yield _ n' -> pure (Rec.Loop n')
    Await be  -> be # unAwait \_ y _ -> pure (Rec.Done (absurdExchange y))
