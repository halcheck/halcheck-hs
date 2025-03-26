{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UnicodeSyntax #-}

module Language.Hedgehog (Gen) where

import Control.Monad (ap, liftM)
import Control.Monad.Gen (MonadGen (..), MonadSample (..))
import Data.Tree (Tree (..))

import qualified Hedgehog.Internal.Gen as HH
import qualified Hedgehog.Internal.Range as HH.Range
import qualified Hedgehog.Internal.Seed as HH.Seed
import qualified Hedgehog.Internal.Tree as HH

newtype Gen a = Gen {runGen ∷ HH.Gen a}
  deriving (Monad)

instance Functor Gen where
  fmap = liftM

instance Applicative Gen where
  pure = Gen . pure
  (<*>) = ap

instance MonadGen Gen where
  label _ = Gen . runGen
  chooseInt n | n < 0 = error "chooseInt: out of range"
  chooseInt n = Gen (HH.integral_ (HH.Range.constant 0 n))
  shrinkInt n = Gen (HH.shrink (\i → if i == 0 then [1 .. n] else []) (pure 0))

instance MonadSample Gen where
  name _ = "hedgehog"
  sampleIO (Gen m) = do
    σ ← HH.Seed.random
    case HH.evalGen 30 σ m of
      Nothing → error "failed sample"
      Just x → pure (go x)
   where
    go (HH.Tree (HH.Node x xs)) = Node x (map go xs)
