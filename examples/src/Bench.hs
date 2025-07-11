{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnicodeSyntax #-}

module Bench where

import qualified Language.Falsify as FF
import qualified Language.FalsifyHC as FF'
import qualified Language.Hedgehog as HH
import qualified Language.HedgehogHC as HH'
import qualified Language.QuickCheck as QC
import qualified Language.QuickCheckHC as QC'

import qualified Example.NonInterference.Register as Register
import qualified Example.NonInterference.Stack as Stack

import Control.DeepSeq (NFData (..))
import Control.Monad (replicateM)
import Control.Monad.Gen (MonadGen, MonadSample (name), label, sampleIO, Monitored)
import Control.Monad.Reader (ReaderT (runReaderT))
import Criterion.Main (Benchmark, bench, bgroup, defaultMain, nfIO, perRunEnv)
import Data.Graph (outdegree)
import Data.Proxy (Proxy (..))
import Data.Tree (Tree (..), rootLabel)
import Example.Bool (bool)
import Example.Graph (connectedGraph, graph)
import Example.Lambda (expr)
import Example.List (distinctList, list, sortedList)
import Example.Pathological (pathological)
import Example.Tree (binarySearchTree, redBlackTree, tree)

newtype NoNF a = NoNF {getNoNF ∷ a}

instance NFData (NoNF a) where
  rnf _ = ()

iters ∷ Int
iters = 1000

testGen ∷ ∀ a m. (NFData a, MonadSample m) ⇒ m a → Benchmark
testGen m =
  bgroup
    (name (Proxy @m))
    [bench "gen" (nfIO (replicateM iters (rootLabel <$> sampleIO m)))]

testShrink ∷ ∀ a m. (NFData a, MonadSample m) ⇒ (a → Bool) → m a → Benchmark
testShrink p m =
  bgroup
    (name (Proxy @m))
    [bench "shrink" (perRunEnv env (pure . map run . getNoNF))]
 where
  env = NoNF <$> replicateM iters (sampleIO m)
  run t = not (p (rootLabel t)) && (any run (subForest t) || True)

test ∷ ∀ a. (NFData a) ⇒ String → (a → Bool) → (∀ m. (MonadGen m) ⇒ m a) → Benchmark
test n p m =
  bgroup
    n
    [ testGen (m ∷ HH.Gen a)
    , testShrink p (m ∷ HH.Gen a)
    , testGen (m ∷ HH'.Gen a)
    , testShrink p (m ∷ HH'.Gen a)
    , testGen (m ∷ Monitored HH'.Gen a)
    , testShrink p (m ∷ Monitored HH'.Gen a)
    , testGen (m ∷ FF.Gen a)
    , testShrink p (m ∷ FF.Gen a)
    , testGen (m ∷ FF'.Gen a)
    , testShrink p (m ∷ FF'.Gen a)
    , testGen (m ∷ Monitored FF'.Gen a)
    , testShrink p (m ∷ Monitored FF'.Gen a)
    , testGen (m ∷ QC.Gen a)
    , testGen (m ∷ QC'.Gen a)
    , testGen (m ∷ Monitored QC'.Gen a)
    ]

main ∷ IO ()
main =
  defaultMain
    [ test "bool" not bool
    , test "pathological" id pathological
    , test "list" and (runReaderT (list bool) 30)
    , test "sorted-list" and (runReaderT (sortedList bool) 30)
    -- , test "distinct-list" and (runReaderT (distinctList bool) 30)
    , test "tree" and (runReaderT tree 10)
    , test "binary-search-tree" or (runReaderT binarySearchTree 10)
    , test "red-black-tree" or (runReaderT redBlackTree 10)
    , test "graph" (all (<= 2) . outdegree) (runReaderT graph 30)
    , test "connected-graph" (all (<= 2) . outdegree) (runReaderT connectedGraph 30)
    , test "lambda" (const False) (runReaderT expr 30)
    , test
        "variation-state"
        (uncurry Register.ssni)
        ((,) <$> label 0 Register.ruleTable <*> (label 1 Register.flags >>= label 2 . Register.variationState))
    , test
        "as-naive"
        (const False)
        (runReaderT Stack.naive 30)
    , test
        "as-weighted"
        (const False)
        (runReaderT Stack.weighted 30)
    , test
        "as-sequence"
        (const False)
        (runReaderT Stack.sequence' 30)
    , test
        "as-by-exec"
        (const False)
        (runReaderT (Stack.byExec 8) 30)
    , test
        "as-by-exec-variational"
        (const False)
        (runReaderT (Stack.byExecVariational 8) 30)
    ]
