{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use record patterns" #-}
{-# HLINT ignore "Redundant bracket" #-}

module Example.NonInterference.Register.Instructions where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import Example.NonInterference.Register.Labels
import Example.NonInterference.Register.Memory

type RegPtr = Int

data Pointer = Ptr Block Int
  deriving (Generic, NFData, Eq, Show, Read)

data Value
  = VInt Int
  | VPtr Pointer
  | VLab Label
  deriving (Generic, NFData, Eq, Show, Read)

data Atom = Atom Value Label
  deriving (Generic, NFData, Eq, Show, Read)

data PtrAtom = PAtm Int Label
  deriving (Generic, NFData, Eq, Show, Read)

data BinOpT
  = BAdd
  | BMult
  | BFlowsTo
  | BJoin
  | BEq
  deriving (Generic, NFData, Eq, Show, Read)

evalBinop ∷ BinOpT → Value → Value → Maybe Value
evalBinop BAdd (VInt x) (VInt y) = Just . VInt $ x + y
evalBinop BMult (VInt x) (VInt y) = Just . VInt $ x * y
evalBinop BJoin (VLab l1) (VLab l2) = Just . VLab $ lub l1 l2
evalBinop BFlowsTo (VLab l1) (VLab l2) = Just . VInt $ flows l1 l2
evalBinop BEq v1 v2 = Just $ VInt $ if v1 == v2 then 1 else 0
evalBinop _ _ _ = Nothing

-- Conversion to register machine.
data Instr
  = Lab RegPtr RegPtr
  | MLab RegPtr RegPtr
  | PcLab RegPtr
  | BCall RegPtr RegPtr RegPtr
  | BRet
  | PutLab Label RegPtr
  | Noop
  | Put Int RegPtr
  | BinOp BinOpT RegPtr RegPtr RegPtr
  | Jump RegPtr
  | Bnz Int RegPtr
  | Load RegPtr RegPtr
  | Store RegPtr RegPtr
  | Write RegPtr RegPtr
  | Upgrade RegPtr RegPtr
  | Alloc RegPtr RegPtr RegPtr
  | PSetOff RegPtr RegPtr RegPtr
  | Halt
  | PGetOff RegPtr RegPtr
  | MSize RegPtr RegPtr
  | Mov RegPtr RegPtr
  deriving (Generic, NFData, Show, Eq, Read)

data InstrKind
  = PUT
  | MOV
  | LOAD
  | STORE
  | BINOP
  | NOOP
  | HALT
  | JUMP
  | BNZ
  | BCALL
  | BRET
  | PUTLAB
  | LAB
  | PCLAB
  | ALLOC
  | WRITE
  | UPGRADE
  | PGETOFF
  | PSETOFF
  | MSIZE
  | MLAB
  deriving (Generic, NFData, Show, Eq, Read, Ord)

allInstrKind ∷ [InstrKind]
allInstrKind =
  [ PUT
  , MOV
  , LOAD
  , STORE
  , BINOP
  , NOOP
  , HALT
  , JUMP
  , BNZ
  , BCALL
  , BRET
  , PUTLAB
  , LAB
  , PCLAB
  , ALLOC
  , WRITE
  , UPGRADE
  , PGETOFF
  , PSETOFF
  , MSIZE
  , MLAB
  ]

opcodeOfInstr ∷ Instr → Maybe InstrKind
opcodeOfInstr (Lab _ _) = Just LAB
opcodeOfInstr (MLab _ _) = Just MLAB
opcodeOfInstr (PcLab _) = Just PCLAB
opcodeOfInstr (BCall _ _ _) = Just BCALL
opcodeOfInstr (BRet) = Just BRET
opcodeOfInstr (PutLab _ _) = Just PUTLAB
opcodeOfInstr (Noop) = Just NOOP
opcodeOfInstr (Put _ _) = Just PUT
opcodeOfInstr (BinOp _ _ _ _) = Just BINOP
opcodeOfInstr (Jump _) = Just JUMP
opcodeOfInstr (Bnz _ _) = Just BNZ
opcodeOfInstr (Load _ _) = Just LOAD
opcodeOfInstr (Store _ _) = Just STORE
opcodeOfInstr (Write _ _) = Just WRITE
opcodeOfInstr (Upgrade _ _) = Just UPGRADE
opcodeOfInstr (Alloc _ _ _) = Just ALLOC
opcodeOfInstr (PSetOff _ _ _) = Just PSETOFF
opcodeOfInstr (PGetOff _ _) = Just PGETOFF
opcodeOfInstr (MSize _ _) = Just MSIZE
opcodeOfInstr (Mov _ _) = Just MOV
opcodeOfInstr (Halt) = Nothing
