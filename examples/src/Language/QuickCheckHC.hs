{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UnicodeSyntax #-}

module Language.QuickCheckHC (Gen) where

import Control.Monad (ap)
import Control.Monad.Gen (MonadGen (..), MonadSample (..))
import System.Random (uniform)

import qualified Test.QuickCheck.Gen as QC
import qualified Test.QuickCheck.Random as QC

newtype Gen a = Gen (QC.Gen a)
  deriving (Functor)

instance Applicative Gen where
  pure x = Gen (pure x)
  (<*>) = ap
  _ *> m = m
  m <* _ = m

instance Monad Gen where
  Gen (QC.MkGen m) >>= f = Gen $ QC.MkGen \seed size →
    let Gen (QC.MkGen m') = f (m seed size)
     in m' seed size
  (>>) = (*>)

instance MonadGen Gen where
  label l (Gen m) = Gen (QC.MkGen (QC.unGen m . permute l))
  chooseInt n = Gen (QC.chooseInt (0, n))
  shrinkInt _ = pure 0

permute ∷ Int → QC.QCGen → QC.QCGen
permute l s = QC.mkQCGen (l + fst (uniform s))

instance MonadSample Gen where
  name _ = "quickcheck-hc"
  sampleIO (Gen m) = pure <$> QC.generate m
