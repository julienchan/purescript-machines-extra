module Data.Machine.Is
  ( Is(..)
  , refl
  ) where

import Prelude

import Data.Monoid (class Monoid)
import Data.Leibniz (type (~))
import Unsafe.Coerce (unsafeCoerce)


data Is a b = Refl (b ~ a)

refl :: forall a. Is a a
refl = Refl id

instance eqIs :: Eq (Is a b) where
  eq _ _ = true

instance ordIs :: Ord (Is a b) where
  compare _ _ = EQ

instance semigroupIs :: Semigroup (Is a a) where
  append _ _ = refl

instance monoidIs :: Monoid (Is a a) where
  mempty = refl

instance semigroupouidIs :: Semigroupoid Is where
  compose (Refl k) (Refl t) = unsafeCoerce refl

instance categoryIs :: Category Is where
  id = refl
