{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UnicodeSyntax #-}

module Example.Tree where

import Control.Monad.Gen (MonadGen (..), frequency, shrinkWith)
import Control.Monad.Reader (MonadReader (..))
import Data.Maybe (isJust)
import Data.Tree (Tree (..))
import Example.List (isSorted)

treeNoShrink ∷ (MonadGen m, MonadReader Int m) ⇒ m (Tree Bool)
treeNoShrink = Node <$> label 0 (range False True) <*> label 1 do
  n ← ask
  frequency
    [ (1, pure [])
    ,
      ( n
      , do
          l ← local (`div` 2) (label 0 treeNoShrink)
          r ← local (`div` 2) (label 1 treeNoShrink)
          pure [l, r]
      )
    ]

tree ∷ (MonadGen m, MonadReader Int m) ⇒ m (Tree Bool)
tree = shrinkWith shrinkTree treeNoShrink

shrinkTree ∷ Tree Bool → [Tree Bool]
shrinkTree (Node b xs) = bShrinks ++ xsShrinks
  where
    bShrinks = [Node False xs | b == True]
    xsShrinks = [Node b (ls ++ [x'] ++ rs) | (ls, x, rs) ← splits xs, x' ← shrinkTree x]

splits ∷ [a] → [([a], a, [a])]
splits [] = []
splits (x:xs) = ([], x, xs) : [(x:ls, y, rs) | (ls, y, rs) ← splits xs]

binarySearchTree ∷ (MonadGen m, MonadReader Int m) ⇒ m (Tree Bool)
binarySearchTree = shrinkWith (filter (isSorted . toList) . shrinkTree) (go 0)
  where
    go i = do
      t ← label i treeNoShrink
      if isSorted (toList t) then pure t else go (i + 1)

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

redBlackTree ∷ (MonadGen m, MonadReader Int m) ⇒ m (Tree Bool)
redBlackTree = shrinkWith (filter isRBTree . shrinkTree) (go 0)
  where
    isRBTree t = isSorted (toList t) && (isJust (isRed t) || isJust (isBlack t))
    go i = do
      t ← label i treeNoShrink
      if isRBTree t then pure t else go (i + 1)
