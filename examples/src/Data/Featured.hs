{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnicodeSyntax #-}

module Data.Featured (Featured (..), dist, totalVariation, mannWhitneyU, kolmogorovSmirnov) where

import Control.DeepSeq (NFData)
import Data.Foldable (toList)
import Data.List (transpose)
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (..))
import Data.Tree (Tree (..))
import Data.Vector.Unboxed (fromList)
import Statistics.Test.KolmogorovSmirnov (Test (..), TestResult (Significant), kolmogorovSmirnovTest2)
import Statistics.Test.MannWhitneyU (PositionTest (..), mannWhitneyUtest)
import Statistics.Types (mkPValue, pValue)

import Data.Array (Array)
import Data.Map (Map)
import qualified Data.Map as Map

class (NFData a) ⇒ Featured a where
  header ∷ Proxy a → [String]
  features ∷ a → [Double]

instance Featured Bool where
  header _ = ["Truthiness"]
  features b = [if b then 1 else 0]

instance Featured Int where
  header _ = ["Value"]
  features i = [fromIntegral i]

instance (Featured a) ⇒ Featured [a] where
  header Proxy = "Size" : map ("Average " ++) (header (Proxy @a))
  features [] = 0 : map (const 0) (header (Proxy @a))
  features xs = fromIntegral (length xs) : map average (transpose (map features xs))

instance (Featured a) ⇒ Featured (Tree a) where
  header Proxy = "Depth" : header (Proxy @[a])
  features t = fromIntegral (depth t) : features (toList t)

instance (Featured a, Featured b) ⇒ Featured (a, b) where
  header Proxy = map ("Left " ++) (header (Proxy @a)) ++ map ("Right " ++) (header (Proxy @b))
  features (t, u) = features t ++ features u

instance (NFData i, Featured a) ⇒ Featured (Array i a) where
  header Proxy = header (Proxy @[a])
  features xs = features (toList xs)

average ∷ [Double] → Double
average [] = 0
average xs = sum xs / fromIntegral (length xs)

depth ∷ Tree a → Int
depth (Node _ []) = 0
depth (Node _ xs) = 1 + maximum (map depth xs)

dist ∷ (Ord a) ⇒ [a] → Map a Double
dist xs = (/ fromIntegral (length xs)) <$> Map.fromListWith (+) (map (,1) xs)

totalVariation ∷ (Ord a) ⇒ Map a Double → Map a Double → Double
totalVariation p q = 0.5 * sum (abs <$> Map.unionWith (-) p q)

mannWhitneyU ∷ (Featured a) ⇒ [a] → [a] → [Bool]
mannWhitneyU xs ys =
  zipWith
    (\us vs → fromJust (mannWhitneyUtest SamplesDiffer (mkPValue 0.05) (fromList us) (fromList vs)) == Significant)
    (transpose (map features xs))
    (transpose (map features ys))

kolmogorovSmirnov ∷ (Featured a) ⇒ [a] → [a] → [(Double, Double)]
kolmogorovSmirnov xs ys =
  zipWith
    ( \us vs →
        let Test p q _ = fromJust (kolmogorovSmirnovTest2 (fromList us) (fromList vs))
         in (pValue p, q)
    )
    (transpose (map features xs))
    (transpose (map features ys))
