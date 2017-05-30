module Test.Main where

import Prelude
import Control.Monad.Aff (Aff, launchAff, delay)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Class (liftEff)
import Control.Monad.Eff.Console (CONSOLE, logShow)
import Control.Monad.Trans.Class (lift)

import Data.Machine.Plan (PlanT, yield, await)
import Data.Machine.Internal (runRecT_, runRec, construct, repeatedly)
import Data.Machine.Process (ProcessT, (<~))
import Data.Machine.Source (unfoldT, SourceT)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Newtype (wrap)


simples :: forall m k. PlanT k String m Unit
simples = yield "hello"

printer :: forall a e. Show a => ProcessT (Aff (console :: CONSOLE | e)) a Unit
printer = repeatedly do
  v <- await
  liftEff $ logShow v

nats :: forall e. Int -> SourceT (Aff (console :: CONSOLE | e)) Int
nats = unfoldT go
  where
  go r =
    if r < 10000
      then do
        delay (wrap 10.00)
        pure $ (Just (Tuple r (r + 1)))
      else do
        delay (wrap 10.00)
        liftEff $ logShow "Closed"
        pure $ Nothing

main :: forall eff. Eff (exception :: EXCEPTION, console :: CONSOLE | eff) Unit
main = void $ launchAff do
  liftEff $ logShow (runRec (construct simples))
  runRecT_ $ printer <~ nats 0
