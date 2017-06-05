module Data.Machine.Internal.FreePlus
  ( FreePlus
  , ChoicesView(..)
  , EffectView(..)
  , liftF
  , wrapF
  , hoistFree
  , foldFree
  , runFreeM
  , substFree
  , toView
  , fromView
  ) where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Plus (class Plus, empty)
import Control.Alternative (class Alternative)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Control.Monad.Trans.Class (class MonadTrans)
import Control.MonadPlus (class MonadZero, class MonadPlus)

import Data.CatList as C
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

import Unsafe.Coerce (unsafeCoerce)

-- | a Free Monad Plus
data FreePlus f a
  = FreePlus (C.CatList (FreePlus f Val)) (C.CatList (ExpF f))
  | FImpure (f (FreePlus f a))
  | FPure a

data ChoicesView f a
  = MZero
  | MPlus (EffectView f a) (FreePlus f a)

data EffectView f a
  = Pure a
  | Impure (f (FreePlus f a))

newtype ExpF f = ExpF (Val -> FreePlus f Val)

data Val

-- | Lift an impure value described by the generating type constructor `f` into
-- | the free monad plus.
liftF :: forall f. Functor f => f ~> FreePlus f
liftF f = FImpure (FPure <$> f)

-- | suspend a functor to FreePlus
wrapF :: forall f a. f (FreePlus f a) -> FreePlus f a
wrapF = FImpure

-- | Use a natural transformation to change the generating type constructor of a
-- | free monad.
hoistFree :: forall f g. Functor f => Functor g => (f ~> g) -> FreePlus f ~> FreePlus g
hoistFree k = substFree (liftF <<< k)

foldFree :: forall f m. Functor f => MonadRec m => MonadPlus m => (f ~> m) -> FreePlus f ~> m
foldFree k = tailRecM go
  where
  go :: forall a. FreePlus f a -> m (Step (FreePlus f a) a)
  go f = case toView f of
    MZero               -> empty
    MPlus (Pure a) _    -> Done <$> pure a
    MPlus (Impure ff) g -> Loop <$> (k ff <|> pure g)

runFreeM
  :: forall f m a
   . Functor f
  => MonadRec m
  => MonadPlus m
  => (f (FreePlus f a) -> m (FreePlus f a))
  -> FreePlus f a
  -> m a
runFreeM k = tailRecM go
  where
  go :: FreePlus f a ->  m (Step (FreePlus f a) a)
  go f = case toView f of
    MZero               -> Done <$> empty
    MPlus (Pure a) g    -> Done <$> pure a
    MPlus (Impure ff) g -> Loop <$> (k ff <|> pure g)

substFree :: forall f g. Functor f => (f ~> FreePlus g) -> FreePlus f ~> FreePlus g
substFree k = go
  where
  go :: FreePlus f ~> FreePlus g
  go f = case toView f of
    MZero               -> empty
    MPlus (Pure a) g    -> pure a >>= \x -> go (pure x <|> g)
    MPlus (Impure fs) g -> k fs   >>= \x -> go (x <|> g)

toView :: forall f a. Functor f => FreePlus f a -> ChoicesView f a
toView = go
  where
  go (FPure x)      = MPlus (Pure x) empty
  go (FImpure x)    = MPlus (Impure x) empty
  go (FreePlus m f) = case C.uncons m of
    Nothing          -> MZero
    Just (Tuple h t) -> case go $ unsafeCoerceFree h of
      MZero          -> go (unsafeCoerceFree $ FreePlus t f)
      MPlus ch ct ->
        let rest = FreePlus (unsafeCoerceFree' ct `C.cons` t) f
        in case ch of
          Impure xx -> MPlus (Impure (map (\yy -> bindFree yy f) xx)) rest
          Pure x    -> case C.uncons f of
            Nothing -> MPlus (Pure x) rest
            Just (Tuple hc tc) ->
              go $ bindFree (unsafeCoerceFree $ runExpF hc $ unsafeCoerceVal' x) tc <|> rest

  unsafeCoerceFree :: FreePlus f Val -> FreePlus f a
  unsafeCoerceFree = unsafeCoerce

  unsafeCoerceFree' :: FreePlus f a -> FreePlus f Val
  unsafeCoerceFree' = unsafeCoerce

  runExpF :: ExpF f -> (Val -> FreePlus f Val)
  runExpF (ExpF k) = k

  unsafeCoerceVal' :: a -> Val
  unsafeCoerceVal' = unsafeCoerce

  unsafeCoerceVal :: Val -> a
  unsafeCoerceVal = unsafeCoerce

bindFree :: forall f a b. FreePlus f a -> C.CatList (ExpF f) -> FreePlus f b
bindFree (FreePlus m r) f = FreePlus m (r <> f)
bindFree m f = if C.null f then unsafeCoerceM m else FreePlus (catSingle (unsafeCoerceFree m)) f
  where
  unsafeCoerceM :: FreePlus f a -> FreePlus f b
  unsafeCoerceM = unsafeCoerce

  unsafeCoerceFree :: FreePlus f a -> FreePlus f Val
  unsafeCoerceFree = unsafeCoerce

fromView :: forall f a. ChoicesView f a -> FreePlus f a
fromView MZero = empty
fromView (MPlus x y) = fromEffView x <|> y

fromEffView :: forall f a. EffectView f a -> FreePlus f a
fromEffView (Pure a)   = FPure a
fromEffView (Impure a) = FImpure a

catSingle :: forall a. a -> C.CatList a
catSingle a = C.cons a C.CatNil

instance functorFreePlus :: Functor (FreePlus f) where
  map k f = pure <<< k =<< f

instance applyFreePlus :: Apply (FreePlus f) where
  apply = ap

instance applicativeFreePlus :: Applicative (FreePlus f) where
  pure = FPure

instance bindFreePlus :: Bind (FreePlus f) where
  bind m f = bindFree m (catSingle $ ExpF $ unsafeCoerceBind f)
    where
    unsafeCoerceBind :: forall a b. (a -> FreePlus f b) -> Val -> FreePlus f Val
    unsafeCoerceBind = unsafeCoerce

instance monadFreePluss :: Monad (FreePlus f)

instance altFreePlus :: Alt (FreePlus f) where
  alt x0 y0 = case x0, y0 of
    x@(FreePlus ml cl), y@(FreePlus mr cr) ->
      case C.null cl, C.null cr of
        true, true -> FreePlus (ml `C.append` mr) C.empty
        _, _       -> FreePlus (catSingle (unsafeAlt x) `C.snoc` unsafeAlt y) C.empty
    xx, yy -> FreePlus (catSingle (unsafeAlt xx) `C.snoc` (unsafeAlt yy)) C.empty

    where
      unsafeAlt :: forall a. FreePlus f a -> FreePlus f Val
      unsafeAlt = unsafeCoerce

instance plusFreePlus :: Plus (FreePlus f) where
  empty = FreePlus C.empty C.empty

instance alternativeFreePlus :: Alternative (FreePlus f)

instance monadZeroFreePlus :: MonadZero (FreePlus f)

instance monadPlusFreePlus :: MonadPlus (FreePlus f)

instance monadTransFreePlus :: MonadTrans FreePlus where
  lift = liftF

instance freeMonadRec :: MonadRec (FreePlus f) where
  tailRecM k a = k a >>= case _ of
    Loop b -> tailRecM k b
    Done r -> pure r
