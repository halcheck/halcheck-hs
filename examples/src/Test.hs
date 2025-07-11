{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module Test where

import Language.Syntax (Dist, dist', toHH, toHH', toQC, toQC')

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Gen (MonadGen)
import Control.Monad.Reader (runReaderT)
import Data.Map (toList)
import Example.Bool (bool)
import Example.Graph (graph)
import Example.Lambda (type_, expr)
import Example.List (list)
import Example.Pathological (pathological)
import Example.Tree (tree)

test1 ∷ (Ord a, Show a) ⇒ Dist a → Dist a → IO ()
test1 m₁ m₂ = do
  let d₁ = dist' m₁
      d₂ = dist' m₂
      go [] [] = pure ()
      go ((t₁, p₁) : xs₁) ((t₂, p₂) : xs₂)
        | t₁ < t₂ = assertFailure ("p₁: " ++ show p₁ ++ ", p₂: 0, t: " ++ show t₁)
        | t₁ > t₂ = assertFailure ("p₁: 0, p₂: " ++ show p₂ ++ ", t: " ++ show t₂)
        | p₁ /= p₂ = assertFailure ("p₁: " ++ show p₁ ++ ", p₂: " ++ show p₂ ++ ", t: " ++ show t₂)
        | otherwise = go xs₁ xs₂
      go ((t, p) : _) [] = assertFailure ("p₁: " ++ show p ++ ", p₂: 0, t: " ++ show t)
      go [] ((t, p) : _) = assertFailure ("p₁: 0, p₂: " ++ show p ++ ", t: " ++ show t)
  go (toList d₁) (toList d₂)

test ∷ (Ord a, Show a) ⇒ String → (∀ m. (MonadGen m) ⇒ m a) → TestTree
test n m =
  testGroup
    n
    [ testCase "QC/QC'" (test1 (toQC m) (toQC' m))
    , testCase "HH/HH'" (test1 (toHH m) (toHH' m))
    ]

main ∷ IO ()
main =
  defaultMain $
    testGroup
      "Tests"
      [ test "bool" bool
      , test "pathological" pathological
      , test "list" (runReaderT (list bool) 4)
      , test "tree" (runReaderT (tree bool) 3)
      , test "graph" (runReaderT graph 4)
      , test "type" (runReaderT type_ 4)
      , test "expr" (runReaderT expr 1)
      ]
