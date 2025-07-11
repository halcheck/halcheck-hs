{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UnicodeSyntax #-}

module Example.Tree where

import Control.Monad.Gen (MonadGen (..), frequency)
import Control.Monad.Reader (MonadReader (..))
import Data.Maybe (isJust)
import Data.Tree (Tree (..))
import Example.List (isSorted)

tree ∷ (MonadGen m, MonadReader Int m) ⇒ m a → m (Tree a)
tree m =
  Node <$> label 0 m <*> label 1 do
    n ← ask
    frequency
      [ (1, pure [])
      ,
        ( n
        , do
            l ← local (`div` 2) (label 1 (tree m))
            r ← local (`div` 2) (label 2 (tree m))
            pure [l, r]
        )
      ]

binarySearchTree ∷ (MonadGen m, MonadReader Int m, Ord a) ⇒ m a → m (Tree a)
binarySearchTree m = do
  t ← label 0 (tree m)
  if isSorted (toList t) then pure t else label 1 (binarySearchTree m)

toList ∷ Tree a → [a]
toList (Node x []) = [x]
toList (Node x [t, u]) = toList t ++ [x] ++ toList u
toList (Node _ _) = error "toList: not binary tree"

isRed ∷ Tree a → Maybe Int
isRed (Node _ []) = Nothing
isRed (Node _ [l, r])
  | Just i ← isBlack l, Just j ← isBlack r, i == j = Just i
  | otherwise = Nothing
isRed _ = Nothing

isBlack ∷ Tree a → Maybe Int
isBlack (Node _ []) = Just 0
isBlack (Node _ [l, r])
  | Just i ← isBlack l, Just j ← isBlack r, i == j = Just (i + 1)
  | Just i ← isBlack l, Just j ← isRed r, i == j + 1 = Just (i + 1)
  | Just i ← isRed l, Just j ← isBlack r, i + 1 == j = Just (i + 1)
  | Just i ← isRed l, Just j ← isRed r, i + 1 == j + 1 = Just (i + 1)
  | otherwise = Nothing
isBlack _ = Nothing

redBlackTree ∷ (MonadGen m, MonadReader Int m, Ord a) ⇒ m a → m (Tree a)
redBlackTree m = do
  t ← label 0 (tree m)
  if isSorted (toList t) && (isJust (isRed t) || isJust (isBlack t))
    then pure t
    else label 1 (redBlackTree m)
