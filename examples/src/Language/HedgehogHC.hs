{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UnicodeSyntax #-}

module Language.HedgehogHC (Gen) where

import Control.Monad (ap, liftM)
import Control.Monad.Gen (MonadGen (..), MonadSample (..))
import Data.Tree (Tree (Node))

import qualified Hedgehog.Internal.Gen as HH
import qualified Hedgehog.Internal.Range as HH.Range
import qualified Hedgehog.Internal.Seed as HH.Seed
import qualified Hedgehog.Internal.Tree as HH

newtype Gen a = Gen {runGen ∷ HH.Gen a}

instance Functor Gen where
  fmap = liftM

instance Applicative Gen where
  pure = Gen . pure
  (<*>) = ap

instance Monad Gen where
  m >>= f = Gen $ HH.GenT \size seed → do
    x ← HH.runGenT size seed (runGen m)
    HH.runGenT size seed (runGen (f x))

instance MonadGen Gen where
  label l m = Gen $ HH.GenT \size seed → HH.runGenT size (permute l seed) (runGen m)
  chooseInt n = Gen (HH.integral_ (HH.Range.constant 0 n))
  shrinkInt n = Gen (HH.shrink (\i → if i == 0 then [1 .. n] else []) (pure 0))

permute ∷ Int → HH.Seed.Seed → HH.Seed.Seed
permute l s = HH.Seed.from (fromIntegral l + fst (HH.Seed.nextWord64 s))

instance MonadSample Gen where
  name _ = "hedgehog-hc"
  sampleIO (Gen m) = do
    σ ← HH.Seed.random
    case HH.evalGen 0 σ m of
      Nothing → error "failed sample"
      Just x → pure (go x)
   where
    go (HH.Tree (HH.Node x xs)) = Node x (map go xs)
