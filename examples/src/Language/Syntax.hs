{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UnicodeSyntax #-}

module Language.Syntax (
  Dist (..),
  dist,
  dist',
  Prune (..),
  Relabel (..),
  toQC,
  toHH,
  toQC',
  toHH',
) where

import Control.Applicative (asum)
import Control.Monad (ap, join, liftM)
import Control.Monad.Gen (MonadGen (..))
import Control.Monad.Reader (MonadReader (..), ReaderT (..))
import Control.Monad.State (MonadState (..), StateT (..))
import Data.Bifunctor (Bifunctor (second))
import Data.Ratio (Ratio)
import Data.Tree (Tree (..))

import Data.Map (Map)
import qualified Data.Map as Map

-- Distributions

newtype Dist a = Dist {runDist ∷ StateT (Map ([Int], Ratio Int) Bool) (ReaderT [Int] []) (Tree a)}
  deriving (Functor)

instance Applicative Dist where
  pure = Dist . pure . pure
  (<*>) = ap

instance Monad Dist where
  m >>= f = Dist do
    x ← runDist m
    y ← mapM (runDist . f) x
    pure (join y)

instance MonadGen Dist where
  label i (Dist m) = Dist (local (i :) m)
  choose 0 = pure False
  choose 1 = pure True
  choose p = Dist do
    ls ← ask
    e ← get
    case Map.lookup (ls, p) e of
      Just b → pure (Node b [])
      Nothing → do
        b ← asum [pure True, pure False]
        put (Map.insert (ls, p) b e)
        pure (Node b [])
  shrinkInt i = Dist (pure (Node 0 (map pure [1 .. i])))
  shrink x xs = Dist (pure (Node x (map pure xs)))

dist ∷ Dist a → [(Tree a, Ratio Int)]
dist (Dist m) =
  map
    (second (product . map (\((_, p), b) → if b then p else 1 - p) . Map.toList))
    (runReaderT (runStateT m Map.empty) [])

dist' ∷ (Ord a) ⇒ Dist a → Map (Tree a) (Ratio Int)
dist' = Map.fromListWith (+) . dist

-- Pruning

newtype Prune m a = Prune {prune ∷ m a}
  deriving (Functor, Applicative, Monad)

instance (MonadGen m) ⇒ MonadGen (Prune m) where
  label l (Prune m) = Prune (label l m)
  choose p = Prune (choose p)
  range a b = Prune (range a b)
  chooseInt n = Prune (chooseInt n)
  shrinkInt _ = Prune (pure 0)
  shrink x _ = Prune (pure x)

-- Relabeling

newtype Relabel m a = Relabel {relabel ∷ m a}

instance (MonadGen m) ⇒ Functor (Relabel m) where
  fmap = liftM

instance (MonadGen m) ⇒ Applicative (Relabel m) where
  pure = Relabel . pure
  (<*>) = ap

instance (MonadGen m) ⇒ Monad (Relabel m) where
  Relabel m >>= f = Relabel (label 0 m >>= label 1 . relabel . f)

instance (MonadGen m) ⇒ MonadGen (Relabel m) where
  label _ = id
  choose p = Relabel (choose p)
  range a b = Relabel (range a b)
  chooseInt n = Relabel (chooseInt n)
  shrinkInt n = Relabel (shrinkInt n)
  shrink x xs = Relabel (shrink x xs)

-- Language-specific transformations

toQC ∷ Prune (Relabel m) a → m a
toQC = relabel . prune

toQC' ∷ Prune m a → m a
toQC' = prune

toHH ∷ Relabel m a → m a
toHH = relabel

toHH' ∷ m a → m a
toHH' = id
