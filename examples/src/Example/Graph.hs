{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UnicodeSyntax #-}

module Example.Graph (graph, connectedGraph) where

import Control.Monad (filterM)
import Control.Monad.Gen (MonadGen (..))
import Control.Monad.Reader (MonadReader, asks)
import Data.Array (bounds)
import Data.Graph (Graph, buildG, components, edges)
import Example.Bool (bool)

graph ∷ (MonadGen m, MonadReader Int m) ⇒ m Graph
graph = do
  n ← asks (ceiling . (sqrt ∷ Double → Double) . fromIntegral)
  sz ← label 0 (range 0 n)
  es ←
    filterM
      ( \(i, j) →
          if i == j
            then return False
            else label i (label j bool)
      )
      ((,) <$> [1 .. sz] <*> [1 .. sz])
  return (buildG (1, sz) es)

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
