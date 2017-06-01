module Benchmark.Main (main) where

import Prelude

import Control.Monad.Aff (Aff)
import Control.Monad.Eff (Eff)
import Control.Monad.Rec.Class (forever)
import Control.Coroutine as Co

import Data.Identity (Identity)
import Data.Newtype (unwrap)
import Data.Foldable as F
import Data.Lazy (defer, force) as Z

import Test.QuickCheck.Arbitrary (arbitrary)
import Test.QuickCheck.Gen (vectorOf)

import Benchotron.Core (Benchmark, BenchEffects, benchFn, mkBenchmark)
import Benchotron.UI.Console (runSuite)

import Data.Machine.Process as M
import Data.Machine.Source as M
import Data.Machine.Internal as M
import Data.Machine.Plan as MP
import Benchmark.Machine.Plan as OP

import Pipes.Prelude as P
import Pipes as P
import Pipes.Core as P
import Pipes.Internal (Proxy) as P

drainM :: forall o e. M.ProcessT (Aff e) Int o -> Array Int ->  Aff e Unit
drainM m v = M.runRecT_ (sourceM v M.~> m)

drainP :: forall e a. P.Proxy Unit Int Unit a (Aff e) Unit -> Array Int ->  Aff e Unit
drainP p v = P.runEffectRec $ P.for (sourceP v P.>-> p) P.discard

drainCo :: forall e a. Co.Consumer Int (Aff e) Unit -> Array Int -> Aff e Unit
drainCo p v = Co.runProcess $ Co.pullFrom p (sourceC v)

sourceM :: Array Int -> M.Source Int
sourceM a = M.source a

sourceP :: forall m. Monad m => Array Int -> P.Producer_ Int m Unit
sourceP = P.each

sourceC :: forall m. Monad m => Array Int -> Co.Producer Int m Unit
sourceC xs = F.foldr (\a p -> Co.emit a *> p) (pure unit) xs

constructOl :: forall k o m a. Monad m => OP.PlanT k o m a -> M.MachineT m k o
constructOl m = M.MachineT (OP.runPlanT m
  (const (pure M.Stop))
  (\o k -> pure (M.Yield o (Z.defer \_ -> M.MachineT $ Z.force k)))
  (\f k g -> pure (M.mkAwait (M.MachineT <<< f) k (Z.defer \_ -> M.MachineT $ Z.force g)))
  (pure M.Stop))

leftBindSmallPlanT :: Benchmark
leftBindSmallPlanT = mkBenchmark $
  { slug: "left-bind-small plan monad"
  , title: "Left associated binds (small - 100 inputs per size)"
  , sizes: [1, 2, 3, 4, 5, 10, 20, 30, 40, 50, 100, 250, 500, 1000]
  , sizeInterpretation: "Number of binds"
  , inputsPerSize: 100
  , gen: \n -> vectorOf n arbitrary
  , functions: [ benchFn "Plan simple" (M.runRecT_ <<< constructOl <<< bindsOl)
               , benchFn "Plan codensity" (M.runRecT_ <<< M.construct <<< binds)
               ]
  }
  where
  binds :: forall k. Array Int -> MP.PlanT k Int Identity Unit
  binds as = F.foldl (\b a -> b >>= const (MP.yield a)) (MP.yield 1) as

  bindsOl :: forall k. Array Int -> OP.PlanT k Int Identity Unit
  bindsOl as = F.foldl (\b a -> b >>= const (OP.yield a)) (OP.yield 1) as

-- | Pipe doesn't stack safe
benchMapping :: Benchmark
benchMapping = mkBenchmark $
  { slug: "mapping"
  , title: "Stream mapping"
  , sizes: [1, 3, 5, 7, 10, 15 ] <#> (_ * 100)
  , sizeInterpretation: "number of stream to map"
  , inputsPerSize: 1
  , gen: \n -> vectorOf n arbitrary
  , functions: [ benchFn "Machine" (drainM (M.mapping (add 1)))
               , benchFn "Pipe" (drainP (P.map (add 1)))
               , benchFn "Coroutine" (drainCo (mapTr `Co.transformConsumer` mapCo))
               ]
  }
  where
  mapTr = forever (Co.transform (add 1))
  mapCo = forever do
    v <- Co.await
    pure unit

main = runSuite [benchMapping, leftBindSmallPlanT]
