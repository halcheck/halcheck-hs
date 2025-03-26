{-# HLINT ignore "Redundant $" #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Example.NonInterference.Stack where

import Control.Monad.Gen (MonadGen, shrinkWith)
import Control.Monad.RWS (MonadReader)
import Example.NonInterference.Stack.Flags (Flaggy (getFlags), TMUDriver, getFlagsRef)
import Example.NonInterference.Stack.Generation (genByExec, genByExecVariational, genNaive, genSequence, genWeighted)
import Example.NonInterference.Stack.Labels (Arbitrary (shrinks))
import Example.NonInterference.Stack.Machine (AS)
import Example.NonInterference.Stack.Observable (Observable (vary))
import Example.NonInterference.Stack.ObservableInst ()
import System.IO.Unsafe (unsafePerformIO)

instance Flaggy TMUDriver where
  getFlags = unsafePerformIO $ getFlagsRef

naive ∷ (MonadGen m, MonadReader Int m) ⇒ m AS
naive = shrinkWith (take 10 . shrinks) genNaive

weighted ∷ (MonadGen m, MonadReader Int m) ⇒ m AS
weighted = shrinkWith (take 10 . shrinks) genWeighted

sequence' ∷ (MonadGen m, MonadReader Int m) ⇒ m AS
sequence' = shrinkWith (take 10 . shrinks) genSequence

byExec ∷ (MonadGen m, MonadReader Int m) ⇒ Int → m AS
byExec = shrinkWith (take 10 . shrinks) . genByExec

byExecVariational ∷ (MonadGen m, MonadReader Int m) ⇒ Int → m AS
byExecVariational i = shrinkWith (take 10 . shrinks) (genByExecVariational i vary)
