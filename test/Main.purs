module Test.Main where

import Prelude
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, logShow)

import Data.Machine.Plan (PlanT, yield)
import Data.Machine.Types (run, construct)

simples :: forall m k. PlanT k String m Unit
simples = yield "hello"

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  logShow (run (construct simples))
