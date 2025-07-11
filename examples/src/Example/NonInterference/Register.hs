{-# LANGUAGE UnicodeSyntax #-}

module Example.NonInterference.Register where

import Control.Monad.Gen (MonadGen (label), element, frequency, range, shrinkWith)
import Example.NonInterference.Register.Flags (CollectF (..), Flags (..), GenInstrType (..), GenType (..), MemType (..), QCMode (..), TestProperty (..))
import Example.NonInterference.Register.Generation (genVariationState)
import Example.NonInterference.Register.Instructions (Atom)
import Example.NonInterference.Register.Machine (State)
import Example.NonInterference.Register.Memory (Mem)
import Example.NonInterference.Register.Mutate (mutateTable)
import Example.NonInterference.Register.Primitives (IMem, Variation)
import Example.NonInterference.Register.Rules (RuleTable, defaultTable)
import Example.NonInterference.Register.SSNI (propSSNI)
import Example.NonInterference.Register.Shrinking (shrinkV)

flags ∷ (MonadGen m) ⇒ m Flags
flags =
  Flags
    <$> label 0 (element [ModeQuickCheck, ModePrintTable])
    <*> label 1 (element [GenByExec, GenSSNI])
    <*> label 2 (element [Naive, DiscardUniform])
    <*> label 3 (element [MemList, MemMap])
    <*> label 4 (element [TestLLNI, TestSSNI, TestMSNI, TestEENI, TestEENI_Weak])
    <*> label 5 (range 5 30)
    <*> label 6 (range 0 100)
    <*> label 7 (frequency [(1, pure Nothing), (3, Just <$> range 0 100)])
    <*> label 8 (range 0 100)
    <*> label 9 (element [False, True])
    <*> label 10 (element [False, True])
    <*> label 11 (range 0 100)
    <*> label 12 (element [False, True])
    <*> label 13 (element [CollectNothing, CollectInstrCode])

ruleTable ∷ (MonadGen m) ⇒ m RuleTable
ruleTable = element (defaultTable : mutateTable defaultTable)

variationState ∷ (MonadGen m) ⇒ Flags → m (Variation (State IMem (Mem Atom)))
variationState = shrinkWith shrinkV . genVariationState

ssni ∷ RuleTable → Variation (State IMem (Mem Atom)) → Bool
ssni = propSSNI
