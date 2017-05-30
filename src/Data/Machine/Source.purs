module Data.Machine.Source
  ( Source
  , SourceT
  , source
  , cap
  , plug
  , unfold
  , unfoldT
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)

import Data.Foldable (class Foldable, foldr, for_)
import Data.Machine.Types ( MachineT(..), Machine, Step(..), encased, stopped, unAwait'
                          , construct)
import Data.Machine.Process (Process, (<~))
import Data.Machine.Plan (yield)
import Data.Maybe (Maybe)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))

-- | A 'Source' never reads from its inputs.
type Source b = forall k. Machine k b

-- | A 'SourceT' never reads from its inputs, but may have monadic side-effects.
type SourceT m b = forall k. MachineT m k b

source :: forall f b. Foldable f => f b -> Source b
source fb = foldr go stopped fb
  where
    go x m = encased $ Yield x m

cap :: forall a b. Process a b -> Source a -> Source b
cap l r = l <~ r

plug :: forall m k o. Monad m => MachineT m k o -> SourceT m o
plug (MachineT m) = MachineT $ m >>= \x -> case x of
  Yield o k     -> pure (Yield o (plug k))
  Stop          -> pure Stop
  Await ba      -> ba # unAwait' \_ _ h -> unwrap $ plug h

unfold :: forall r a. (r -> Maybe (Tuple a r)) -> r -> Source a
unfold k seed = construct (go seed)
  where
  go r = for_ (k r) $ \(Tuple a r') -> do
    _ <- yield a
    go r'

unfoldT :: forall m r a. Monad m => (r -> m (Maybe (Tuple a r))) -> r -> SourceT m a
unfoldT k seed = construct (go seed)
  where
    go r = do
      opt <- lift $ k r
      for_ opt $ \(Tuple a r') -> do
        _ <- yield a
        go r'
