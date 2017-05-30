module Data.Machine.Source
  ( Source
  , SourceT
  , source
  , plug
  , unfold
  , unfoldT
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)

import Data.Foldable (class Foldable, foldr)
import Data.Lazy (defer, force) as Z
import Data.Machine.Internal ( MachineT(..), Machine, Step(..), encased, stopped, unAwait
                          , construct)
import Data.Machine.Plan (yield)
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

unfold :: forall r a. (r -> Maybe (Tuple a r)) -> r -> Source a
unfold k seed = construct (go seed)
  where
  go r = case k r of
    Nothing -> pure unit
    Just (Tuple a r') -> do
      _ <- yield a
      go r'

unfoldT :: forall m r a. Monad m => (r -> m (Maybe (Tuple a r))) -> r -> SourceT m a
unfoldT k seed = construct (go seed)
  where
  go r = do
    opt <- lift $ k r
    case opt of
      Nothing -> pure unit
      Just (Tuple a r') -> do
        _ <- yield a
        go r'
