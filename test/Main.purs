module Test.Main where

import Prelude

import Control.Monad.Aff (Aff, launchAff, delay, nonCanceler, Canceler)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Class (liftEff)
import Control.Monad.Eff.Console (CONSOLE, logShow, log)
import Control.Monad.Trans.Class (lift)

import Data.Array ((..))
import Data.Foldable (for_)
import Data.Machine.Plan (PlanT, yield, await)
import Data.Machine.Internal (runRecT_, runRec, construct, repeatedly)
import Data.Machine.Process (ProcessT, (<~), mapping)
import Data.Machine.Source (SourceT, unfoldT, source)
import Data.Machine.Pipe (Server', Client', request, respond, runEffectRec, (>>~))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Newtype (wrap)
import Data.Function.Uncurried (Fn3, runFn3)

--------------------------------------------------------------------------------
-- Readline --------------------------------------------------------------------
--------------------------------------------------------------------------------

foreign import data Readline :: Type

foreign import createReadline :: forall e. Eff e Readline

foreign import closeReadline :: forall e. Readline -> Eff e Unit

foreign import _askQuestion :: forall e. Fn3 (Canceler e) String Readline (Aff e String)

askQuestion :: forall e. String -> Readline -> Aff e String
askQuestion s r = runFn3 _askQuestion nonCanceler s r

--------------------------------------------------------------------------------
-- simple machines -------------------------------------------------------------
--------------------------------------------------------------------------------

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
    if r < 100000
      then do
        delay (wrap 10.00)
        pure $ (Just (Tuple r (r + 1)))
      else do
        delay (wrap 10.00)
        liftEff $ logShow "Closed"
        pure $ Nothing

--------------------------------------------------------------------------------
-- Example Pipe, bidirectional communication -----------------------------------
--------------------------------------------------------------------------------

data Req  = Ping | Ask String | Close

data Resp = Started | Pong | Chunk String | Closed

-- | The server
serverPipe :: forall e r. Server' Req Resp (Aff (console :: CONSOLE | e)) r
serverPipe = construct do
  _ <- liftEff $ log "Bootstrapping server..."
  rl <- liftEff $ createReadline
  req <- respond Started
  loop rl req
  where
  loop rl Ping = do
    _ <- lift $ delay (wrap 100.00)
    _ <- liftEff $ log "Get a Ping"
    respond Pong >>= loop rl
  loop rl (Ask qst) = do
    _ <- liftEff $ log "Get ReadLn"
    li <- lift $ askQuestion qst rl
    respond (Chunk li) >>= loop rl
  loop rl Close = do
    _ <- liftEff $ log "Good bye" *> closeReadline rl
    respond Closed

clientPipe :: forall e r. Client' Req Resp (Aff (console :: CONSOLE | e)) r
clientPipe = construct go
  where
  go = request Ping >>= \v ->
    case v of
      Pong -> do
        _ <- liftEff $ log "Receive PONG"
        for_ ["What's your name? ", "Do you know Purescript? ", "oh, got it."] \q -> do
          s <- request (Ask q)
          hdAnswer s
        void $ request Close
      _     -> void do
        _ <- liftEff $ log "unexpected respond"
        request Close
  hdAnswer (Chunk s) = void do
    liftEff $ log $ "Got message: " <> s
  hdAnswer _ = void do
    liftEff $ log $ "unexpected respond"

main :: forall eff. Eff (exception :: EXCEPTION, console :: CONSOLE | eff) Unit
main = void $ launchAff do
  -- runEffectRec $ serverPipe >>~ const clientPipe
  runRecT_ $ mapping (add 1) <~ source (1..1000)
  -- liftEff $ logShow (runRec (construct simples))
  -- runRecT_ $ printer <~ nats 0
