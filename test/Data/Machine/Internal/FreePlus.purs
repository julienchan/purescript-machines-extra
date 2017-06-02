module Test.Data.Machine.Internal.FreePlus where

import Prelude

import Control.MonadZero (guard, (<|>), empty)
import Control.Monad.Aff (Aff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Eff.Class (liftEff)
import Data.Machine.Internal.FreePlus (FreePlus, foldFree, liftF)


-- | Target DSL that we will actually run
data TeletypeF a
  = PutStrLn String a
  | GetLine (String -> a)

derive instance functorTeletypeF :: Functor TeletypeF

type Teletype = FreePlus TeletypeF

putStrLn :: String -> Teletype Unit
putStrLn s = liftF $ PutStrLn s unit

getLine :: Teletype String
getLine = liftF $ GetLine id

-- | Interpreter for `Teletype`, producing an effectful output
runTeletype :: forall eff. Teletype ~> Aff (console :: CONSOLE | eff)
runTeletype = foldFree go
  where
  go :: TeletypeF ~> Aff (console :: CONSOLE | eff)
  go (PutStrLn s next) = liftEff (log s) $> next
  go (GetLine k) = pure (k "fake input")

-- | Initial DSL that we will reinterpret as TeletypeF
data InitialF a
  = Greet (String -> a)
  | Farewell a

derive instance functorInitialF :: Functor InitialF

type Initial = FreePlus InitialF

greet :: Initial String
greet = liftF $ Greet id

farewell :: Initial Unit
farewell = liftF $ Farewell unit

-- | Interpreter for `Initial`, producing a `Teletype` output. `foldFree` allows
-- | us to map one action in `InitialF` to multiple actions in `TeletypeF` (see
-- | the `Greet` case - we're expanding one `InitialF` action into 3 `TeletypeF`
-- | actions).
runInitial :: Initial ~> Teletype
runInitial initial = foldFree go initial
  where
  go :: InitialF ~> Teletype
  go (Greet k) = do
    name <- getLine
    putStrLn $ "Hello " <> name
    putStrLn "How's things?"
    pure (k name)
  go (Farewell next) = putStrLn "Bye!" $> next

-- | Our test "script" in the Initial DSL
test :: Initial String
test = do
  name <- empty <|> greet
  name2 <- greet <|> empty
  guard (name == name2)
  farewell
  pure name

-- Run the thing
main :: forall eff. Aff (console :: CONSOLE | eff) Unit
main = do
  a <- runTeletype (runInitial test)
  liftEff $ log $ "Input name while running: " <> a