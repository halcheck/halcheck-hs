{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module Example.Lambda where

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Applicative (Alternative (..))
import Control.DeepSeq (NFData)
import Control.Monad (ap, guard, join)
import Control.Monad.Except (runExceptT)
import Control.Monad.Gen (MonadGen (..), element, frequency, mapG, shrinkWith, tryAll)
import Control.Monad.Reader (MonadReader (ask, local))
import Data.Bifunctor (Bifunctor (..))
import Data.Foldable (Foldable (..), toList)
import Data.List (nub, sort)
import Data.Maybe (isJust, maybeToList)
import Data.Void (Void, absurd)
import GHC.Generics (Generic)

data Type a
  = TInt
  | TBool
  | TFun (Type a) (Type a)
  | TVar a
  | TList (Type a)
  deriving (Eq, Foldable, Functor, Generic, Ord, NFData, Show, Traversable)

instance Applicative Type where
  pure = TVar
  (<*>) = ap

instance Monad Type where
  TInt >>= _ = TInt
  TBool >>= _ = TBool
  TFun x y >>= f = TFun (x >>= f) (y >>= f)
  TVar x >>= f = f x
  TList x >>= f = TList (x >>= f)

(<:) ∷ (Ord a) ⇒ Type Void → Type a → Maybe (Map a (Type Void))
TInt <: TInt = Just Map.empty
TBool <: TBool = Just Map.empty
TFun α β <: TFun α' β' = do
  m₁ ← α <: α'
  m₂ ← β <: β'
  sequence (Map.unionWith (\x y → if x == y then x else Nothing) (fmap Just m₁) (fmap Just m₂))
TList τ <: TList τ' = τ <: τ'
τ <: TVar x = Just (Map.singleton x τ)
_ <: _ = Nothing

-- 50
type_ ∷ (MonadGen m, MonadReader Int m) ⇒ m (Type Void)
type_ = do
  n ← ask
  frequency
    [ (1, pure TInt)
    , (1, pure TBool)
    , (min n 1, TList <$> local (subtract 1) type_)
    ,
      ( min n 1
      , TFun
          <$> label 0 (local ((`div` 2) . subtract 1) type_)
          <*> label 1 (local ((`div` 2) . subtract 1) type_)
      )
    ]

type Name = String

data Expr a
  = EVar a
  | ECon (Type Void) Name
  | ELam (Type Void) (Expr (Maybe a))
  | EApp (Expr a) (Expr a)
  deriving (Eq, Generic, Foldable, Functor, Ord, NFData, Show, Traversable)

instance Applicative Expr where
  pure = EVar
  (<*>) = ap

instance Monad Expr where
  EVar x >>= f = f x
  ECon τ c >>= _ = ECon τ c
  ELam τ e >>= f = ELam τ (e >>= maybe (EVar Nothing) (fmap Just . f))
  EApp e₁ e₂ >>= f = EApp (e₁ >>= f) (e₂ >>= f)

typeOf ∷ (a → Type Void) → Expr a → Maybe (Type Void)
typeOf ρ (EVar x) = Just (ρ x)
typeOf _ (ECon τ _) = Just τ
typeOf ρ (ELam τ e) = TFun τ <$> typeOf (maybe τ ρ) e
typeOf ρ (EApp e₁ e₂) = do
  TFun α β ← typeOf ρ e₁
  τ ← typeOf ρ e₂
  guard (α == τ)
  pure β

type Rule m a =
  [(Name, Type Name)] → -- Constants
  [(a, Type Void)] → -- Variables
  Type Void → -- Target Type
  [m (Expr a)]

ruleVar ∷ (MonadGen m) ⇒ Rule m a
ruleVar χ ρ α = [pure (ECon α e) | (e, β) ← χ, isJust (α <: β)] ++ [pure (EVar x) | (x, β) ← ρ, α == β]

ruleLam ∷ (MonadReader Int m, MonadGen m, Alternative m) ⇒ Rule m a
ruleLam χ ρ τ = do
  TFun α β ← pure τ
  pure do
    n ← ask
    guard (n > 0)
    let ρ' = (Nothing, α) : map (first Just) ρ
    ELam α <$> label 0 (local (subtract 1) (exprOf χ ρ' β))

-- Returns an underapproximation of the set of types for which we can generate terms.
univ ∷ (Ord a) ⇒ [Type a] → [Type Void]
univ ρ =
  [b | a ← ρ, b ← traverse (const []) a]
    ++ [ join e
       | TFun a b ← ρ -- Pick function type
       , c ← ρ -- Pick argument type
       , d ← traverse (const []) c -- Argument type should be mono
       , Just m ← [d <: a] -- Argument type should match parameter type
       , e ← traverse (maybeToList . flip Map.lookup m) b -- Instantiate result type
       ]

ruleApp ∷ (MonadReader Int m, MonadGen m, Alternative m) ⇒ Rule m a
ruleApp χ ρ β = pure do
  n ← ask
  guard (n > 0)
  α ← label 0 (element τs)
  e₁ ← label 1 (local ((`div` 2) . subtract 1) (exprOf χ ρ (TFun α β)))
  e₂ ← label 2 (local ((`div` 2) . subtract 1) (exprOf χ ρ α))
  pure (EApp e₁ e₂)
 where
  τs = univ (map snd χ ++ map (fmap absurd . snd) ρ)

ruleInferVar ∷ (MonadReader Int m, MonadGen m, Alternative m) ⇒ Rule m a
ruleInferVar χ ρ β = do
  (x, τ) ← ρ
  case params τ of
    Nothing → empty
    Just τs → pure do
      n ← ask
      guard (n > 0)
      es ← local ((`div` length τs) . subtract 1) (mapG (exprOf χ ρ) τs)
      pure (foldl' EApp (EVar x) es)
 where
  params α | α == β = Just []
  params (TFun τ α) | Just τs ← params α = Just (τ : τs)
  params _ = Nothing

ruleInferCon ∷ (MonadReader Int m, MonadGen m, Alternative m) ⇒ Rule m a
ruleInferCon χ ρ β = do
  (x, τ) ← χ
  (τs, σ) ← take 3 (params τ)
  let free = nub (sort (concatMap toList τs))
  pure do
    n ← ask
    guard (n > 0)
    σ' ← label 0 (Map.fromAscList <$> mapG (\y → (,) y <$> element τs') free)
    es ← label 1 (local ((`div` length τs) . subtract 1) (mapG (exprOf χ ρ . toVoid . apply σ') τs))
    pure (foldl' EApp (ECon (toVoid (apply (Map.union σ σ') τ)) x) es)
 where
  toVoid = fmap (const undefined)

  τs' = univ (map snd χ ++ map (fmap absurd . snd) ρ)

  params α =
    [([], σ) | σ ← maybeToList (β <: α)]
      ++ [(apply σ τ : τs, σ) | TFun τ γ ← [α], (τs, σ) ← params γ]

  apply ∷ (Ord a) ⇒ Map a (Type Void) → Type a → Type a
  apply σ τ = do
    x ← τ
    case Map.lookup x σ of
      Nothing → pure x
      Just τ' → fmap absurd τ'

exprOf ∷ (MonadReader Int m, MonadGen m, Alternative m) ⇒ [(Name, Type Name)] → [(a, Type Void)] → Type Void → m (Expr a)
exprOf χ ρ τ = tryAll (concatMap (\f → f χ ρ τ) [ruleVar, ruleLam, ruleApp, ruleInferVar, ruleInferCon])

expr ∷ (MonadReader Int m, MonadGen m) ⇒ m (Expr Void)
expr = do
  τ ← label 0 type_
  r ← label 1 (runExceptT (exprOf χ [] τ))
  case r of
    Left () → label 2 expr
    Right x → shrinkWith (shrinks absurd) (pure x)
 where
  χ =
    [(show i, TInt) | i ← [-10 .. 10 ∷ Int]]
      ++ [ ("True", TBool)
         , ("False", TBool)
         , ("[]", TList (TVar "α"))
         , ("(:)", TFun (TVar "α") (TFun (TList (TVar "α")) (TList (TVar "α"))))
         , ("id", TFun (TVar "α") (TVar "α"))
         ]

shrinks ∷ ∀ a. (Eq a) ⇒ (a → Type Void) → Expr a → [Expr a]
shrinks ρ e = rule₁ e ++ rule₂ e ++ rule₃ e ++ rec e
 where
  rule₁ ∷ Expr a → [Expr a]
  rule₁ _ = [e' | e' ← subterms e, typeOf ρ e' == typeOf ρ e]
   where
    subterms ∷ Expr b → [Expr b]
    subterms (EApp e₁ e₂) = e₁ : e₂ : subterms e₁ ++ subterms e₂
    subterms (ELam _ e') = [e''' | e'' ← subterms e', e''' ← maybeToList (sequence e'')]
    subterms _ = []

  rule₂ ∷ Expr a → [Expr a]
  rule₂ e' =
    case typeOf ρ e' of
      Nothing → error "rule₂: IMPOSSIBLE"
      Just τ | e'' ← the τ, e' /= e'' → [e'']
      _ → []
   where
    the TInt = ECon TInt "0"
    the TBool = ECon TBool "False"
    the (TList τ) = ECon (TList τ) "[]"
    the (TFun α β) = ELam α (fmap Just (the β))
    the (TVar x) = absurd x

  rule₃ ∷ Expr a → [Expr a]
  rule₃ (EApp (ELam _ e₁) e₂) = [e₁ >>= maybe e₂ pure]
  rule₃ _ = []

  rec ∷ Expr a → [Expr a]
  rec (ELam τ e') = ELam τ <$> shrinks (maybe τ ρ) e'
  rec (EApp e₁ e₂) = (EApp e₁ <$> shrinks ρ e₂) ++ (flip EApp e₂ <$> shrinks ρ e₁)
  rec _ = []
