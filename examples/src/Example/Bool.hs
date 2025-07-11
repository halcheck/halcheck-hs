{-# LANGUAGE UnicodeSyntax #-}

module Example.Bool where

import Control.Monad.Gen (MonadGen, range, shrink, label)

bool ∷ (MonadGen m) ⇒ m Bool
bool = do
  b ← range False True
  if b then shrink True [False] else pure False
