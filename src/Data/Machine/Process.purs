module Data.Machine.Process
  ( Process
  , ProcessT
  , echo
  , prepended
  , filtered
  , dropping
  , taking
  , takingWhile
  , droppingWhile
  , (<~), addProcess
  , (~>), flippedAddProcess
  , supply
  , process
  , scan
  , mapping
  , scanMap
  , folding
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)

import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.Rec.Class (Step(..), tailRecM2) as Rec

import Data.Foldable (class Foldable, traverse_, foldr)
import Data.Machine.Internal ( MachineT(..), Machine, Step(..), mkAwait, unAwait
                          , stopped, encased, before, construct)
import Data.Machine.Is (Is(..), refl)
import Data.Lazy (defer, force) as Z
import Data.Leibniz (coerceSymm)
import Data.Machine.Plan (yield, await, stop)
import Data.Monoid (class Monoid, mempty)
import Data.Newtype (unwrap)

type Process a b = Machine (Is a) b

type ProcessT m a b = MachineT m (Is a) b

echo :: forall a. Process a a
echo = go
  where
  go = encased (mkAwait (\t -> encased (Yield t $ Z.defer \_ -> go)) refl (Z.defer \_ -> stopped))

-- | A 'Process' that prepends the elements of a 'Foldable' onto its input, then repeats its input from there.
prepended :: forall f a. Foldable f => f a -> Process a a
prepended fa = before echo (traverse_ yield fa)

filtered :: forall a. (a -> Boolean) -> Process a a
filtered p = go
  where
  go = encased
         $ mkAwait (\a -> if p a then encased (Yield a $ Z.defer \_ -> go) else go)
           refl
           (Z.defer \_ -> stopped)

dropping :: forall a. Int -> Process a a
dropping cnt
  | cnt <= 0  = echo
  | otherwise = encased $ mkAwait (\_ -> dropping (cnt - 1)) refl (Z.defer \_ -> stopped)

taking :: forall a. Int -> Process a a
taking cnt
  | cnt <= 0  = stopped
  | otherwise = encased $
      mkAwait
        (\v -> encased $ Yield v (Z.defer \_ -> taking (cnt - 1)))
        refl
        (Z.defer \_ -> stopped)

takingWhile :: forall a. (a -> Boolean) -> Process a a
takingWhile p = go
  where
  go = encased
         $ mkAwait (\a -> if p a then encased (Yield a $ Z.defer \_ -> go) else stopped)
           refl
           (Z.defer \_ -> stopped)

droppingWhile :: forall a. (a -> Boolean) -> Process a a
droppingWhile p = go
  where
  go = encased
       $ mkAwait (\a -> if p a then go else encased (Yield a $ Z.defer \_ -> echo))
         refl
         (Z.defer \_ -> stopped)

addProcess :: forall m b k c. MonadRec m => ProcessT m b c -> MachineT m k b -> MachineT m k c
addProcess mp0 ma0 = MachineT $ Rec.tailRecM2 go mp0 ma0
  where
  go mp ma = unwrap mp >>= \v -> case v of
    Stop          -> pure (Rec.Done Stop)
    Yield o k     -> pure $ Rec.Done $ Yield o (Z.defer \_ -> Z.force k <~ ma)
    Await be      -> be # unAwait \f (Refl leib) ff -> unwrap ma >>= \u -> case u of
      Stop          -> pure $ Rec.Loop ({a: Z.force ff, b: stopped })
      Yield o k     -> pure $ Rec.Loop ({a: f (coerceSymm leib o),  b: Z.force k})
      Await be'     -> be' # unAwait \g kg fg -> pure $ Rec.Done $
        mkAwait
        (\a -> encased v <~ g a)
        kg
        (Z.defer \_ -> encased v <~ Z.force fg)

infixr 8 addProcess as <~

flippedAddProcess :: forall m b k c. MonadRec m => MachineT m k b -> ProcessT m b c -> MachineT m k c
flippedAddProcess = flip addProcess

infixr 8 flippedAddProcess as ~>

supply :: forall f m a b . Foldable f => Monad m => f a -> ProcessT m a b -> ProcessT m a b
supply = foldr go id
  where
  go :: a -> (ProcessT m a b -> ProcessT m a b) -> ProcessT m a b -> ProcessT m a b
  go x r m = MachineT $ do
    v <- unwrap m
    case v of
      Stop      -> pure Stop
      Await be  -> be # unAwait \f (Refl sym) _ -> unwrap $ r (f (coerceSymm sym x))
      Yield o k -> pure $ Yield o (Z.defer \_ -> go x r $ Z.force k)

process :: forall m k i o. Monad m => (forall a. k a -> i -> a) -> MachineT m k o -> ProcessT m i o
process f (MachineT m) = MachineT (map f' m) where
  f' (Yield o k) = Yield o (Z.defer \_ -> process f $ Z.force k)
  f' Stop        = Stop
  f' (Await be)  = be # unAwait \g kir h -> mkAwait (process f <<< g <<< f kir) refl (map (process f) h)

scan :: forall k b a. Category k => (a -> b -> a) -> a -> Machine (k b) a
scan f s =
  let step t = encased $ Yield t $ Z.defer \_ -> encased $ mkAwait (step <<< f t) id (Z.defer \_ -> stopped)
  in step s

scanMap :: forall k b a. Category k => Monoid b => (a -> b) -> Machine (k a) b
scanMap f = scan (\b a -> append b (f a)) mempty

folding :: forall k b a. Category k => (a -> b -> a) -> a -> Machine (k b) a
folding f s =
  let step t = encased (mkAwait (step <<< f t) id (Z.defer \_ -> encased (Yield t $ Z.defer \_ -> stopped)))
  in  step s

mapping :: forall k a b. Category k => (a -> b) -> Machine (k a) b
mapping f = go
  where
  go = encased (mkAwait (\t -> encased (Yield (f t) (Z.defer \_ -> go))) id (Z.defer \_ -> stopped))
