{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UnicodeSyntax #-}

module Example.Pathological where

import Control.Monad.Gen (MonadGen (..), range, shrink)

pathological ∷ (MonadGen m) ⇒ m Bool
pathological = do
  i ← shrink False [True]
  x ← range False True
  pure (x == i)
