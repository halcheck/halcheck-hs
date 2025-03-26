{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Example.NonInterference.Register.Flags where

import Control.DeepSeq (NFData)
import Data.Data
import GHC.Generics (Generic)

data MemType = MemList | MemMap
  deriving (Generic, NFData, Eq, Show, Read, Typeable, Data)

data GenInstrType = Naive | DiscardUniform
  deriving (Generic, NFData, Eq, Show, Read, Typeable, Data)

data GenType
  = GenByExec
  | GenSSNI
  deriving (Generic, NFData, Eq, Show, Read, Typeable, Data)

data TestProperty
  = TestLLNI
  | TestSSNI
  | TestMSNI
  | TestEENI
  | TestEENI_Weak
  deriving (Generic, NFData, Eq, Show, Read, Typeable, Data)

data QCMode
  = ModeQuickCheck
  | ModePrintTable
  deriving (Generic, NFData, Eq, Show, Read, Typeable, Data)

data CollectF
  = CollectInstrCode
  | CollectNothing
  deriving (Generic, NFData, Eq, Show, Read, Typeable, Data)

data Flags = Flags
  { mode ∷ !QCMode
  , strategy ∷ !GenType
  , genInstrDist ∷ !GenInstrType
  , memType ∷ !MemType
  , testProp ∷ !TestProperty
  , noSteps ∷ !Int
  , maxTests ∷ !Int
  , mutantNo ∷ !(Maybe Int)
  , discardRatio ∷ !Int
  , isVerbose ∷ !Bool
  , printLatex ∷ !Bool
  , timeout ∷ !Int
  , doShrink ∷ !Bool
  , collectF ∷ !CollectF
  }
  deriving (Generic, NFData, Eq, Show, Read, Typeable, Data)

defaultFlags ∷ Flags
defaultFlags =
  Flags
    { mode = ModeQuickCheck
    , strategy = GenByExec
    , genInstrDist = DiscardUniform
    , memType = MemMap
    , testProp = TestMSNI
    , noSteps = 42
    , maxTests = 10000
    , mutantNo = Nothing
    , discardRatio = 10
    , isVerbose = False
    , printLatex = False
    , timeout = 10
    , doShrink = False
    , collectF = CollectNothing
    }

naiveSsniConfig ∷ Flags → Flags
naiveSsniConfig f =
  f
    { strategy = GenSSNI
    , genInstrDist = Naive
    , testProp = TestSSNI
    , noSteps = 2
    }
ssniConfig ∷ Flags → Flags
ssniConfig f = (naiveSsniConfig f){genInstrDist = DiscardUniform}
llniConfig ∷ Flags → Flags
llniConfig f =
  f
    { strategy = GenByExec
    , genInstrDist = DiscardUniform
    , testProp = TestLLNI
    , noSteps = 42
    }
naiveLlniConfig ∷ Flags → Flags
naiveLlniConfig f = (llniConfig f){genInstrDist = Naive}
naiveLLNIListConfig ∷ Flags → Flags
naiveLLNIListConfig f = (naiveLlniConfig f){memType = MemList}
msniConfig ∷ Flags → Flags
msniConfig f = (llniConfig f){genInstrDist = DiscardUniform, testProp = TestMSNI}
naiveMsniConfig ∷ Flags → Flags
naiveMsniConfig f = (msniConfig f){genInstrDist = Naive}
eeniConfig ∷ Flags → Flags
eeniConfig f = (llniConfig f){genInstrDist = Naive, testProp = TestEENI}
eeniWeakConfig ∷ Flags → Flags
eeniWeakConfig f = (eeniConfig f){testProp = TestEENI_Weak}
