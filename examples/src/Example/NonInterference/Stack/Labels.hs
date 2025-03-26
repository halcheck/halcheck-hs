{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Example.NonInterference.Stack.Labels where

import Test.QuickCheck (Arbitrary1 (liftShrink), shrink)

import Control.DeepSeq (NFData)
import Control.Monad.Gen (MonadGen (range), frequency, liftG2, liftG3, liftG4, listOf)
import Control.Monad.RWS (MonadReader)
import Example.NonInterference.Stack.LaTeX
import GHC.Generics (Generic)

-- The very simple lattice we are using
data Label = L | H
  deriving (Generic, NFData, Eq, Ord, Read, Show)

instance LaTeX Label where
  toLaTeX L = "\\low"
  toLaTeX H = "\\high"

instance Arbitrary Label where
  arbitrary = frequency [(1, return L), (1, return H)]
  shrinks lab = [L | lab == H]

-- Arbitrary labeled data
data Labeled a = Labeled {lab ∷ Label, value ∷ a}
  deriving (Generic, NFData, Eq, Ord, Read)

instance Functor Labeled where
  fmap f (Labeled l a) = Labeled l (f a)

instance (Show a) ⇒ Show (Labeled a) where
  show s = show (value s) ++ "@" ++ show (lab s)

instance (LaTeX a) ⇒ LaTeX (Labeled a) where
  toLaTeX (Labeled l a) = toLaTeX a ++ " \\labelsym " ++ toLaTeX l

instance (Arbitrary a) ⇒ Arbitrary (Labeled a) where
  arbitrary = liftG2 Labeled arbitrary arbitrary
  shrinks (Labeled a b) = map (uncurry Labeled) (shrinks (a, b))

-- QuickCheck generator combinator for labeled data
labeled ∷ (MonadGen f, MonadReader Int f) ⇒ f a → f (Labeled a)
labeled = liftG2 Labeled arbitrary

withLab ∷ Labeled a → Label → Labeled a
withLab labeled lab = labeled{lab = lab}
infix 1 `withLab`

class Lub a where
  lub ∷ a → a → a

instance Lub Label where
  lub = max

-- a@l `tainting` b@r == b@(l `lub` r); this allows for an easy
-- way to compute the proper label for some piece of data by combining it with
-- all the other data which affected it; as long as the current data comes last,
-- everything will work properly.
tainting ∷ Labeled a → Labeled b → Labeled b
tainting a b = Labeled (lab a `lub` lab b) (value b)

instance (Num a) ⇒ Num (Labeled a) where
  Labeled l m + Labeled l' m' = Labeled (max l l') (m + m')
  Labeled l m - Labeled l' m' = Labeled (max l l') (m - m')
  Labeled l m * Labeled l' m' = Labeled (max l l') (m * m')
  abs (Labeled l m) = Labeled l (abs m)
  signum (Labeled l m) = Labeled l (signum m)
  fromInteger n = Labeled L (fromInteger n)

class Arbitrary a where
  arbitrary ∷ (MonadGen m, MonadReader Int m) ⇒ m a
  shrinks ∷ a → [a]

instance Arbitrary Int where
  arbitrary = range (-65536) 65536
  shrinks = shrink

instance Arbitrary Bool where
  arbitrary = range False True
  shrinks True = [False]
  shrinks False = []

instance (Arbitrary a, Arbitrary b) ⇒ Arbitrary (a, b) where
  arbitrary = liftG2 (,) arbitrary arbitrary
  shrinks (x, y) = map (,y) (shrinks x) ++ map (x,) (shrinks y)

instance (Arbitrary a, Arbitrary b, Arbitrary c) ⇒ Arbitrary (a, b, c) where
  arbitrary = liftG3 (,,) arbitrary arbitrary arbitrary
  shrinks (x, y, z) = map (,y,z) (shrinks x) ++ map (x,,z) (shrinks y) ++ map (x,y,) (shrinks z)

instance (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d) ⇒ Arbitrary (a, b, c, d) where
  arbitrary = liftG4 (,,,) arbitrary arbitrary arbitrary arbitrary
  shrinks (x, y, z, w) = map (,y,z,w) (shrinks x) ++ map (x,,z,w) (shrinks y) ++ map (x,y,,w) (shrinks z) ++ map (x,y,z,) (shrinks w)

instance (Arbitrary a) ⇒ Arbitrary [a] where
  arbitrary = listOf arbitrary
  shrinks = liftShrink shrinks
