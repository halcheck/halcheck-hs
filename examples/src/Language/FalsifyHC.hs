{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UnicodeSyntax #-}

module Language.FalsifyHC (Gen) where

import Control.Monad (ap, liftM)
import Control.Monad.Gen (MonadGen (..), MonadSample (..))
import System.Random (uniform, uniformR)

import qualified Test.Falsify.Generator as FF
import qualified Test.Falsify.Interactive as FF
import qualified Test.QuickCheck.Random as QC

newtype Gen a = Gen {runGen ∷ QC.QCGen → FF.Gen a}

instance Functor Gen where
  fmap = liftM

instance Applicative Gen where
  pure x = Gen \_ → pure x
  (<*>) = ap

instance Monad Gen where
  Gen m >>= f = Gen \σ → FF.bindWithoutShortcut (m σ) \x → runGen (f x) σ

instance MonadGen Gen where
  label l (Gen m) = Gen (m . permute l)
  chooseInt n = Gen (pure . fst . uniformR (0, n))
  shrinkInt n = Gen (const (FF.shrinkToOneOf 0 [1 .. n]))

permute ∷ Int → QC.QCGen → QC.QCGen
permute l s = QC.mkQCGen (l + fst (uniform s))

instance MonadSample Gen where
  name _ = "falsify-hc"
  sampleIO (Gen m) = QC.newQCGen >>= FF.sample . FF.toShrinkTree . m
