module Data.Machine.Source
  ( Source
  , SourceT
  , source
  , plug
  , unfold
  , unfoldT
  ) where

import Prelude

import Control.Monad.Rec.Class as Rec

import Data.Foldable (class Foldable, foldr)
import Data.Lazy (defer, force) as Z
import Data.Machine.Internal ( MachineT(..), Machine, Step(..), encased, stopped, unAwait)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))

-- | A 'Source' never reads from its inputs.
type Source b = forall k. Machine k b

-- | A 'SourceT' never reads from its inputs, but may have monadic side-effects.
type SourceT m b = forall k. MachineT m k b

source :: forall f b. Foldable f => f b -> Source b
source fb = foldr go stopped fb
  where
    go x m = encased $ Yield x (Z.defer \_ -> m)

plug :: forall m k o. Monad m => MachineT m k o -> SourceT m o
plug (MachineT m) = MachineT $ m >>= \x -> case x of
  Yield o k     -> pure (Yield o (map plug k))
  Stop          -> pure Stop
  Await ba      -> ba # unAwait \_ _ h -> unwrap $ plug (Z.force h)

plugRec :: forall m k o. Rec.MonadRec m => MachineT m k o -> SourceT m o
plugRec m0 = MachineT $ Rec.tailRecM go m0
  where
  go m = unwrap m >>= \x -> case x of
    Yield o k -> pure $ Rec.Done $ (Yield o (map plug k))
    Stop      -> pure $ Rec.Done Stop
    Await ba  -> ba # unAwait \_ _ h -> pure $ Rec.Loop (Z.force h)

unfold :: forall r a. (r -> Maybe (Tuple a r)) -> r -> Source a
unfold k seed = MachineT $ go seed
  where
  go r = case k r of
    Nothing           -> pure Stop
    Just (Tuple a r') -> pure $ Yield a (Z.defer \_ -> MachineT $ go r')

unfoldT :: forall m r a. Monad m => (r -> m (Maybe (Tuple a r))) -> r -> SourceT m a
unfoldT k seed = MachineT $ go seed
  where
  go r = k r >>= \x -> case x of
    Nothing -> pure Stop
    Just (Tuple a r') -> pure $ Yield a (Z.defer \_ -> MachineT $ go r')
