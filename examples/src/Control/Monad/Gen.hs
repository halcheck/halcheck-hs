{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UnicodeSyntax #-}

module Control.Monad.Gen (
  MonadGen (..),
  int,
  range',
  liftG2,
  liftG3,
  liftG4,
  replicateG,
  element,
  oneof,
  frequency,
  tryAll,
  mapG,
  sequenceG,
  foldG,
  shrinkWith,
  MonadSample (..),
  samplePathIO,
  listOf,
) where

import Control.Applicative (Alternative (..))
import Control.Monad (foldM, join)
import Control.Monad.Except (ExceptT (..))
import Control.Monad.Reader (MonadReader (ask), MonadTrans (lift), ReaderT (..))
import Control.Monad.State (MonadState (get, put), evalStateT)
import Data.Proxy (Proxy (..))
import Data.Ratio (Ratio, denominator, numerator, (%))
import Data.Tree (Tree (..))
import Data.Vector.Internal.Check (HasCallStack)
import System.Random (randomRIO)

class (Monad m) ⇒ MonadGen m where
  label ∷ Int → m a → m a

  chooseInt ∷ Int → m Int
  chooseInt = range 0

  choose ∷ Ratio Int → m Bool
  choose p
    | 0 <= p && p <= 1 = (== numerator p) <$> chooseInt (denominator p)
    | otherwise = error ("choose: " ++ show p ++ "∉ [0, 1]")

  range ∷ (HasCallStack, Enum a) ⇒ a → a → m a
  range i j = toEnum <$> go (fromEnum i) (fromEnum j)
   where
    go m n | m > n = error "range: invalid arguments"
    go m n =
      case compare m n of
        EQ → pure m
        GT → error "range: invalid range"
        LT → do
          let o = (m + n) `div` 2
          b ← choose ((o - m + 1) % (n - m + 1))
          if b then go m o else go (o + 1) n

  shrinkInt ∷ Int → m Int
  shrinkInt n = shrink 0 [1 .. n]

  shrink ∷ a → [a] → m a
  shrink x xs = do
    n ← shrinkInt (length xs)
    pure (if n == 0 then x else xs !! (n - 1))

  {-# MINIMAL label, (shrink | shrinkInt), (chooseInt | choose | range) #-}

range' ∷ (Enum a, MonadGen m) ⇒ a → a → m a
range' x y
  | fromEnum x < fromEnum y = range x y
  | fromEnum x > fromEnum y = range y x
  | otherwise = pure x

int ∷ (MonadGen m) ⇒ m Int
int = do
  n ← range (-65536) 65536
  b ← element [False, True]
  pure (if b then n else -n)

replicateG ∷ (MonadGen m) ⇒ Int → m a → m [a]
replicateG n m = mapG id (replicate n m)

liftG2 ∷ (MonadGen m) ⇒ (a → b → c) → m a → m b → m c
liftG2 f m₁ m₂ = f <$> label 0 m₁ <*> label 1 m₂

liftG3 ∷ (MonadGen m) ⇒ (a → b → c → d) → m a → m b → m c → m d
liftG3 f m₁ m₂ m₃ = f <$> label 0 m₁ <*> label 1 m₂ <*> label 2 m₃

liftG4 ∷ (MonadGen m) ⇒ (a → b → c → d → e) → m a → m b → m c → m d → m e
liftG4 f m₁ m₂ m₃ m₄ = f <$> label 0 m₁ <*> label 1 m₂ <*> label 2 m₃ <*> label 3 m₄

mapG ∷ (MonadGen f, Traversable t) ⇒ (a → f b) → t a → f (t b)
mapG f =
  flip evalStateT (0 ∷ Int) . traverse \x → do
    i ← get
    put (i + 1)
    lift (label i (f x))

sequenceG ∷ (MonadGen f, Traversable t) ⇒ t (f a) → f (t a)
sequenceG = mapG id

foldG ∷ (Foldable t, MonadGen m) ⇒ (b → a → m b) → b → t a → m b
foldG op sd xs = snd <$> foldM (\(i, x) r → (,) (i + 1) <$> label i (op x r)) (0 ∷ Int, sd) xs

element ∷ (MonadGen m) ⇒ [a] → m a
element xs = do
  i ← chooseInt (length xs - 1)
  pure (xs !! i)

oneof ∷ (MonadGen m) ⇒ [m a] → m a
oneof = label 1 . join . label 0 . element . zipWith label [0 ..]

frequency ∷ (MonadGen m) ⇒ [(Int, m a)] → m a
frequency ms = do
  let go _ [] = error "IMPOSSIBLE"
      go i ((k, m) : ms') = if i < k then m else go (i - k) ms'
  n ← label 0 (chooseInt (sum (map fst ms) - 1))
  go n (zipWith (\i (k, m) → (k, label i m)) [0 ..] ms)

tryAll ∷ (MonadGen m, Alternative m) ⇒ [m a] → m a
tryAll [] = empty
tryAll ms = do
  i ← label 0 (chooseInt (length ms - 1))
  let (m, ms') = removeAt i ms
  label 1 m <|> label 2 (tryAll ms')
 where
  removeAt ∷ Int → [a] → (a, [a])
  removeAt _ [] = error "removeAt: invalid index"
  removeAt 0 (x : xs) = (x, xs)
  removeAt n (x : xs) = fmap (x :) (removeAt (n - 1) xs)

shrinkWith ∷ (MonadGen m) ⇒ (a → [a]) → m a → m a
shrinkWith f m = m >>= go
 where
  go x = shrink Nothing (map Just (f x)) >>= maybe (pure x) go

instance (MonadGen m) ⇒ MonadGen (ReaderT r m) where
  label l (ReaderT m) = ReaderT (label l . m)
  chooseInt = lift . chooseInt
  choose = lift . choose
  range a b = lift (range a b)
  shrinkInt = lift . shrinkInt
  shrink x xs = lift (shrink x xs)

instance (MonadGen m) ⇒ MonadGen (ExceptT r m) where
  label l (ExceptT m) = ExceptT (label l m)
  chooseInt = lift . chooseInt
  choose = lift . choose
  range a b = lift (range a b)
  shrinkInt = lift . shrinkInt
  shrink x xs = lift (shrink x xs)

class (Monad m) ⇒ MonadSample m where
  name ∷ Proxy m → String
  sampleIO ∷ m a → IO (Tree a)

samplePathIO ∷ (MonadSample m) ⇒ m a → IO [a]
samplePathIO m = sampleIO m >>= go
 where
  go ~(Node x xs) =
    case xs of
      [] → pure [x]
      _ → do
        i ← randomRIO (0, length xs - 1)
        (x :) <$> go (xs !! i)

listOf ∷ (MonadGen f, MonadReader Int f) ⇒ f a → f [a]
listOf m = do
  n ← ask
  s ← label 0 (range 0 n)
  label 1 (replicateG s m)
