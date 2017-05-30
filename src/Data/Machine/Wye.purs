module Data.Machine.Wye where

import Prelude

import Data.Either (Either(..))
import Data.Lazy (defer, force) as Z
import Data.Leibniz (type (~), coerceSymm)
import Data.Machine.Is (Is(..))
import Data.Machine.Internal (MachineT(..), Machine, Step(..), unAwait, mkAwait, stopped, encased)
import Data.Machine.Process (ProcessT, echo, process)
import Data.Machine.Source (SourceT, plug)
import Data.Newtype (unwrap)


data WyeIn a b c
  = WyeL (c ~ a)            -- block waiting on the left input
  | WyeR (c ~ b)            -- block waiting on the right input
  | WyeE (c ~ Either a b)   -- block waiting on either input

-- | A 'Machine' that can read from two input stream in a non-deterministic manner.
type Wye a b c = Machine (WyeIn a b) c

-- | A 'Machine' that can read from two input stream in a non-deterministic manner with monadic side-effects.
type WyeT m a b c = MachineT m (WyeIn a b) c

-- | Compose a pair of pipes onto the front of a 'Wye'.
-- | Precompose a 'Process' onto each input of a 'Wye' (or 'WyeT').
--
-- This is left biased in that it tries to draw values from the 'WyeL' input whenever they are
-- available, and only draws from the 'WyeR' input when 'WyeL' would block.
wye
  :: forall m a' a b b' c
   . Monad m
  => ProcessT m a a'
  -> ProcessT m b b'
  -> WyeT m a' b' c
  -> WyeT m a b c
wye ma mb m = MachineT $ unwrap m >>= \v -> case v of
  Yield o k -> pure $ Yield o $ map (wye ma mb) k
  Stop      -> pure Stop
  Await aw' -> aw' # unAwait \f wyin ff -> case wyin of
    WyeL lpf -> unwrap ma >>= \u -> case u of
      Yield a k -> unwrap <<< wye (Z.force k) mb $ f (coerceSymm lpf a)
      Stop       -> unwrap $ wye stopped mb $ Z.force ff
      Await awl  -> awl # unAwait \g (Refl rpfa) fg ->
        pure $
          mkAwait (\a -> wye (g $ coerceSymm rpfa $ a) mb $ encased v)
          (WyeL id)
          (Z.defer \_ -> wye (Z.force fg) mb $ encased v)
    WyeR rpf -> unwrap mb >>= \u -> case u of
      Yield b k           -> unwrap <<< wye ma (Z.force k) $ f (coerceSymm rpf b)
      Stop                -> unwrap $ wye ma stopped $ Z.force ff
      Await awr           -> awr # unAwait \g (Refl fpfa') fg ->
        pure $
          mkAwait (\b -> wye ma (g $ coerceSymm fpfa' $ b) $ encased v)
          (WyeR id)
          (Z.defer \_ -> wye ma (Z.force fg) $ encased v)
    WyeE epf -> unwrap ma >>= \u -> case u of
      Yield a k -> unwrap <<< wye (Z.force k) mb $ f (coerceSymm epf (Left a))
      Stop      -> unwrap mb >>= \w -> case w of
        Yield b k   -> unwrap <<< wye stopped (Z.force k) <<< f $ coerceSymm epf (Right b)
        Stop        -> unwrap $ wye stopped stopped $ Z.force ff
        Await awre  -> awre # unAwait \g (Refl arf) fg ->
          pure $
            mkAwait (\b -> wye stopped (g $ coerceSymm arf $ b) $ encased v)
            (WyeR id)
            (Z.defer \_ -> wye stopped (Z.force fg) $ encased v)
      Await awle -> awle # unAwait \g (Refl alf) fg -> unwrap mb >>= \w -> case w of
        Yield b k   -> unwrap <<< wye (encased u) (Z.force k) <<< f $ coerceSymm epf $ Right b
        Stop        ->
          pure $
            mkAwait (\a -> wye (g $ coerceSymm alf $ a) stopped $ encased v)
            (WyeL id)
            (Z.defer \_ -> wye (Z.force fg) stopped $ encased v)
        Await awe'  -> awe' # unAwait \h (Refl hrf) fh ->
          pure $
            mkAwait (\c' -> case c' of
                                Left a  -> wye (g $ coerceSymm alf $ a) (encased w) $ encased v
                                Right b -> wye (encased u) (h $ coerceSymm hrf $ b) $ encased v
                    )
           (WyeE id)
           (Z.defer \_ -> wye (Z.force fg) (Z.force fh) $ encased v)

-- | Precompose a pipe onto the left input of a wye.
addL :: forall m a b c d. Monad m => ProcessT m a b -> WyeT m b c d -> WyeT m a c d
addL p = wye p echo

-- | Precompose a pipe onto the right input of a wye.
addR :: forall m a b c d. Monad m => ProcessT m b c -> WyeT m a c d -> WyeT m a b d
addR = wye echo

-- | Tie off one input of a wye by connecting it to a known source.
capR :: forall m a b c. Monad m => SourceT m a -> WyeT m a b c -> ProcessT m b c
capR s t = process (capped Right) (addL s t)

-- | Tie off one input of a wye by connecting it to a known source.
capY :: forall m a b c. Monad m => SourceT m b -> WyeT m a b c -> ProcessT m a c
capY s t = process (capped Left) (addR s t)

-- | Tie off both inputs of a wye by connecting them to known sources.
capWye :: forall m a b c. Monad m => SourceT m a -> SourceT m b -> WyeT m a b c -> SourceT m c
capWye a b = plug <<< wye a b

capped :: forall a b. (a -> Either a a) -> WyeIn a a b -> a -> b
capped _ (WyeL prl) = coerceSymm prl <<< id
capped _ (WyeR prr) = coerceSymm prr <<< id
capped f (WyeE pre) = coerceSymm pre <<< f
