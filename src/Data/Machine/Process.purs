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
  , scanMap
  , folding
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)

import Data.Foldable (class Foldable, traverse_, foldr)
import Data.Machine.Types ( MachineT(..), Machine, Step(..), mkAwait', unAwait'
                          , stopped, encased, before, construct)
import Data.Machine.Is (Is(..), refl)
import Data.Leibniz (coerceSymm)
import Data.Machine.Plan (yield, await, stop)
import Data.Machine.Mealy as M
import Data.Monoid (class Monoid, mempty)
import Data.Newtype (unwrap)

type Process a b = Machine (Is a) b

type ProcessT m a b = MachineT m (Is a) b

echo :: forall a. Process a a
echo = go
  where
  go = encased (mkAwait' (\t -> encased (Yield t go)) refl stopped)

-- | A 'Process' that prepends the elements of a 'Foldable' onto its input, then repeats its input from there.
prepended :: forall f a. Foldable f => f a -> Process a a
prepended fa = before echo (traverse_ yield fa)

filtered :: forall a. (a -> Boolean) -> Process a a
filtered p = go
  where
  go = encased
         $ mkAwait' (\a -> if p a then encased (Yield a go) else go)
           refl
           stopped

dropping :: forall a. Int -> Process a a
dropping cnt
  | cnt <= 0  = echo
  | otherwise = encased (mkAwait' (\_ -> dropping (cnt - 1)) refl stopped)

taking :: forall a. Int -> Process a a
taking cnt
  | cnt <= 0  = stopped
  | otherwise = encased (mkAwait' (\v -> encased $ Yield v (taking (cnt - 1))) refl stopped)

takingWhile :: forall a. (a -> Boolean) -> Process a a
takingWhile p = go
  where
  go = encased
         $ mkAwait' (\a -> if p a then encased (Yield a go) else stopped)
           refl
           stopped

droppingWhile :: forall a. (a -> Boolean) -> Process a a
droppingWhile p = go
  where
  go = encased
       $ mkAwait' (\a -> if p a then go else encased (Yield a echo))
         refl
         stopped

addProcess :: forall m b k c. Monad m => ProcessT m b c -> MachineT m k b -> MachineT m k c
addProcess mp ma = MachineT $ unwrap mp >>= \v -> case v of
  Stop          -> pure Stop
  Yield o k     -> pure $ Yield o (k <~ ma)
  Await be -> be # unAwait' \f (Refl leib) ff -> unwrap ma >>= \u -> case u of
    Stop          -> unwrap $ ff <~ stopped
    Yield o k     -> unwrap $ f (coerceSymm leib o) <~ k
    Await be'     -> be' # unAwait' \g kg fg -> pure $ mkAwait' (\a -> encased v <~ g a) kg (encased v <~ fg)

infixr 9 addProcess as <~

flippedAddProcess :: forall m b k c. Monad m => MachineT m k b -> ProcessT m b c -> MachineT m k c
flippedAddProcess = flip addProcess

infixr 9 flippedAddProcess as ~>

supply :: forall f m a b . Foldable f => Monad m => f a -> ProcessT m a b -> ProcessT m a b
supply = foldr go id
  where
  go :: a -> (ProcessT m a b -> ProcessT m a b) -> ProcessT m a b -> ProcessT m a b
  go x r m = MachineT $ do
    v <- unwrap m
    case v of
      Stop      -> pure Stop
      Await be  -> be # unAwait' \f (Refl sym) _ -> unwrap $ r (f (coerceSymm sym x))
      Yield o k -> pure $ Yield o (go x r k)

process :: forall m k i o. Monad m => (forall a. k a -> i -> a) -> MachineT m k o -> ProcessT m i o
process f (MachineT m) = MachineT (map f' m) where
  f' (Yield o k) = Yield o (process f k)
  f' Stop        = Stop
  f' (Await be)  = be # unAwait' \g kir h -> mkAwait' (process f <<< g <<< f kir) refl (process f h)

scan :: forall k b a. Category k => (a -> b -> a) -> a -> Machine (k b) a
scan f s =
  let step t = encased $ Yield t $ encased $ mkAwait' (step <<< f t) id stopped
  in step s

scanMap :: forall k b a. Category k => Monoid b => (a -> b) -> Machine (k a) b
scanMap f = scan (\b a -> append b (f a)) mempty

folding :: forall k b a. Category k => (a -> b -> a) -> a -> Machine (k b) a
folding f s =
  let step t = encased (mkAwait' (step <<< f t) id (encased (Yield t stopped)))
  in  step s

autoMealy :: forall m a b. Monad m => M.MealyT m a b -> ProcessT m a b
autoMealy = construct <<< go
  where
  go mealy = do
    v <- await
    s <- lift $ M.stepMealy v mealy
    case s of
      M.Emit b mealy' -> do
        _ <- yield b
        go mealy'
      M.Halt -> stop
