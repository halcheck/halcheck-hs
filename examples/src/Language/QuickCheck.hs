{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UnicodeSyntax #-}

module Language.QuickCheck (Gen) where

import Control.Monad.Gen (MonadGen (..), MonadSample (..))

import qualified Test.QuickCheck.Gen as QC

newtype Gen a = Gen (QC.Gen a)
  deriving (Functor, Applicative, Monad)

instance MonadGen Gen where
  label _ m = m
  chooseInt n = Gen (QC.chooseInt (0, n))
  shrinkInt _ = pure 0

instance MonadSample Gen where
  name _ = "quickcheck"
  sampleIO (Gen m) = pure <$> QC.generate m
