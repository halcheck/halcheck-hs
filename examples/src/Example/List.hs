{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

module Example.List where

import Control.Monad.Gen (MonadGen (..))
import Control.Monad.RWS (MonadReader (..))
import Data.List (sort)
import Data.Ratio ((%))

list ∷ (MonadGen m, MonadReader Int m) ⇒ m a → m [a]
list m = do
  n ← ask
  b ← label 0 (choose (1 % (n + 1)))
  if b
    then return []
    else do
      x ← label 1 m
      xs ← label 2 (local (const (n - 1)) (list m))
      shrink (x : xs) [xs]

sortedList ∷ (MonadGen m, MonadReader Int m, Ord a) ⇒ m a → m [a]
sortedList m = do
  xs ← label 0 (list m)
  if isSorted xs then pure xs else label 1 (sortedList m)

isSorted ∷ (Ord a) ⇒ [a] → Bool
isSorted xs = all (uncurry (<=)) (zip xs (tail xs))

distinctList ∷ (MonadGen m, MonadReader Int m, Ord a) ⇒ m a → m [a]
distinctList m = go 0
  where
    go n = do
      xs ← label n (list m)
      if isDistinct xs then pure xs else go (n + 1)

isDistinct ∷ (Ord a) ⇒ [a] → Bool
isDistinct (sort → xs) = all (uncurry (/=)) (zip xs (tail xs))
