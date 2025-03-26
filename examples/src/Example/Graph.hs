{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UnicodeSyntax #-}

module Example.Graph (graph, connectedGraph) where

import Control.Monad (filterM)
import Control.Monad.Gen (MonadGen (..), shrinkWith)
import Control.Monad.Reader (MonadReader, asks)
import Data.Array (bounds)
import Data.Graph (Graph, buildG, components, edges)

graph ∷ (MonadGen m, MonadReader Int m) ⇒ m Graph
graph = do
  n ← asks (ceiling . (sqrt ∷ Double → Double) . fromIntegral)
  sz ← label 0 (range 0 n)
  es ←
    filterM
      ( \(i, j) →
          if i == j
            then return False
            else label i (label j (range False True))
      )
      ((,) <$> [1 .. sz] <*> [1 .. sz])
  es' ← shrinkWith dropAny (pure es)
  return (buildG (1, sz) es')

dropAny ∷ [a] → [[a]]
dropAny [] = []
dropAny (x : xs) = xs : map (x :) (dropAny xs)

invert ∷ Graph → Graph
invert g =
  buildG
    (bot, top)
    (filter (\(x, y) → (x, y) `notElem` es) ((,) <$> [bot .. top] <*> [bot .. top]))
 where
  (bot, top) = bounds g
  es = edges g

connectedGraph ∷ (MonadGen m, MonadReader Int m) ⇒ m Graph
connectedGraph = do
  g ← graph
  return (if length (components g) <= 1 then g else invert g)
