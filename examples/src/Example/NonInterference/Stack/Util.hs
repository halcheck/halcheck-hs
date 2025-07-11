{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
{-# HLINT ignore "Use fmap" #-}

module Example.NonInterference.Stack.Util where

import Control.Arrow
import Control.Monad
import Data.IORef
import Data.List
import System.Random
import Control.Monad.Gen (MonadGen, range')

(-->) ∷ Bool → Bool → Bool
p --> q = not p || q
infixr 1 -->

int ∷ (Num a, Random a, MonadGen f, Enum a) ⇒ f a
int = range' (-10) 10

upfrom ∷ (Num a, Random a, MonadGen f, Enum a) ⇒ a → a → f a
n `upfrom` low = range' low (low + n - 1)

isIndex ∷ Int → [a] → Bool
{-# INLINE isIndex #-}
isIndex a l = a >= 0 && a < length l

update ∷ Int → a → [a] → [a]
update a b xs = take a xs ++ [b] ++ drop (a + 1) xs

bagify ∷ (Ord a) ⇒ [a] → [(a, Int)]
bagify = map (head &&& length) . group . sort

-- qc ∷ (Testable prop) ⇒ Int → prop → IO Bool
-- qc n p = do
--   r ← newIORef True
--   quickCheckWith stdArgs{maxSuccess = n, maxDiscardRatio = 2} $
--     whenFail (writeIORef r False) p
--   ok ← readIORef r
--   -- when ok aggregateResults
--   return ok

strictModify ∷ (Monad m) ⇒ m a → (a → m ()) → (a → a) → m ()
strictModify rd wr f = do
  x ← f `liftM` rd
  x `seq` wr x

modifyIORef' ∷ IORef a → (a → a) → IO ()
modifyIORef' = liftM2 strictModify readIORef writeIORef

{- No longer works with latest QC
    Couldn't match expected type `Test.QuickCheck.Random.QCGen'
                with actual type `StdGen'
pick :: Gen a -> IO a
pick g = do seed <- getStdGen
            return $ unGen g seed 10
-}

allBounded ∷ (Enum a, Bounded a) ⇒ [a]
allBounded = [minBound .. maxBound]

chunks ∷ Int → [a] → [[a]]
chunks _ [] = []
chunks n xs = let (chunk, xs') = splitAt n xs in chunk : chunks n xs'
