{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UnicodeSyntax #-}

module Language.Falsify (Gen) where

import Control.Monad (ap, liftM)
import Control.Monad.Gen (MonadGen (..), MonadSample (..))

import qualified Test.Falsify.Generator as FF
import qualified Test.Falsify.Interactive as FF
import qualified Test.Falsify.Range as FF.Range

newtype Gen a = Gen {runGen ∷ FF.Gen a}

instance Functor Gen where
  fmap = liftM

instance Applicative Gen where
  pure x = Gen (pure x)
  (<*>) = ap

instance Monad Gen where
  Gen m >>= f = Gen (FF.bindWithoutShortcut m (runGen . f))

instance MonadGen Gen where
  label _ m = m
  chooseInt n = Gen (FF.withoutShrinking (FF.int (FF.Range.between (0, n))))
  shrinkInt n = Gen (FF.shrinkToOneOf 0 [1 .. n])

instance MonadSample Gen where
  name _ = "falsify"
  sampleIO (Gen m) = FF.sample (FF.toShrinkTree m)
