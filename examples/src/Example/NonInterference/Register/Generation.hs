{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Use fmap" #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Use <&>" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Example.NonInterference.Register.Generation where

import Control.Monad.Gen

import Control.Monad
import Data.Maybe

import Example.NonInterference.Register.Flags
import Example.NonInterference.Register.Instructions
import Example.NonInterference.Register.Labels
import Example.NonInterference.Register.Machine
import Example.NonInterference.Register.Memory as Memory
import Example.NonInterference.Register.Primitives
import Example.NonInterference.Register.Rules
import Example.NonInterference.Register.Zipper

-- Thread some information for better generation
data Info = MkInfo
  { flags ∷ Flags
  , codeLen ∷ Int
  , dataLen ∷ [(Block, Int)]
  , noRegs ∷ Int
  }

class SmartGen a where
  smartGen ∷ (MonadGen f) ⇒ Info → f a

arbitrary ∷ (MonadGen f) ⇒ f BinOpT
arbitrary = element [BAdd, BMult, BFlowsTo, BJoin, BEq]

shrinks ∷ BinOpT → [BinOpT]
shrinks BMult = [BAdd]
shrinks BEq = [BAdd]
shrinks BJoin = [BAdd]
shrinks BFlowsTo = [BEq]
shrinks BAdd = []

-- Generate a label below another
genLabelBelow ∷ (MonadGen f) ⇒ Label → f Label
genLabelBelow = element . labelsBelow

-- Generate a label in [l1, l2]
genLabelBetweenLax ∷ (MonadGen f) ⇒ Label → Label → f Label
genLabelBetweenLax l1 l2 =
  element $ filter (\l → isLow l1 l) $ labelsBelow l2

-- Generate a label in (l1, l2]
-- CH: comment is wrong
genLabelBetweenStrict ∷ (MonadGen f) ⇒ Label → Label → f Label
genLabelBetweenStrict l1 l2 =
  element $ filter (\l → isLow l1 l && l /= l1) $ labelsBelow l2

instance SmartGen Label where
  smartGen _ = genLabelBelow H

-- Will always produce a valid pointer
instance SmartGen Pointer where
  smartGen (MkInfo _ _ dfs _) = do
    (mf, len) ← label 0 (element dfs)
    addr ← label 1 (range' 0 (len - 1))
    return $ Ptr mf addr

-- Gives some weight to valid instruction pointers
-- CH: for some reason this is currently only used for variation
instance SmartGen Int where
  smartGen (MkInfo _ cl _ _) =
    frequency
      [ (1, pure 0)
      , (10, range' 0 (cl - 1))
      ]

instance SmartGen Value where
  smartGen info@(MkInfo _ cl dfs _) =
    frequency $
      [ -- (1, liftM VInt $ smartGen info)
        (1, liftM VInt $ range' 0 (cl - 1))
      , -- CH: only instruction pointers, wow, no negative ones
        (1, liftM VLab $ smartGen info)
      ]
        ++ [(1, liftM VPtr $ smartGen info) | not $ null dfs]

instance SmartGen Atom where
  smartGen info = liftG2 Atom (smartGen info) (smartGen info)

instance SmartGen PtrAtom where
  smartGen info@(MkInfo _ cl _ _) = do
    liftG2 PAtm (range' 0 (cl - 1)) (smartGen info)

instance SmartGen RegSet where
  smartGen info = fmap RegSet $ replicateG (noRegs info) (smartGen info)

-- Creates a stack element whose PC label is between two labels, strict or lax
-- based on the function argument
smartGenStkElt ∷ (MonadGen f) ⇒ Info → f StkElt
smartGenStkElt info = do
  regs ← label 0 (smartGen info)
  PAtm addr _ ← label 1 (smartGen info)
  target ← label 2 (range' 0 (noRegs info - 1))
  retLab ← label 3 (smartGen info)
  pcLab ← label 4 (smartGen info)
  return $ StkElt (PAtm addr pcLab, retLab, regs, target)

smartGenStack ∷ (MonadGen f) ⇒ PtrAtom → Info → f Stack
smartGenStack pc info =
  frequency
    [ (1, return $ Stack [])
    ,
      ( 9
      , liftM (Stack . return) $
          smartGenStkElt info
      )
    ]

isInt ∷ Atom → Bool
isInt (Atom (VInt _) _) = True
isInt _ = False

isPtr ∷ Atom → Bool
isPtr (Atom (VPtr _) _) = True
isPtr _ = False

isCpt ∷ Int → Atom → Bool
isCpt imemLen (Atom (VInt x) _) = 0 <= x && x < imemLen
isCpt _ _ = False

isLab ∷ Atom → Bool
isLab (Atom (VLab _) _) = True
isLab _ = False

-- Group Register into categories based on their contents
groupRegisters ∷
  Int →
  [Register] →
  [RegPtr] →
  [RegPtr] →
  [RegPtr] →
  [RegPtr] →
  Int →
  ([RegPtr], [RegPtr], [RegPtr], [RegPtr])
groupRegisters il [] dptr cptr num lab n = (dptr, cptr, num, lab)
groupRegisters il (r : rs) dptr cptr num lab n
  | isCpt il r = groupRegisters il rs dptr (n : cptr) (n : num) lab (n + 1)
  | isInt r = groupRegisters il rs dptr cptr (n : num) lab (n + 1)
  | isPtr r = groupRegisters il rs (n : dptr) cptr num lab (n + 1)
  | isLab r = groupRegisters il rs dptr cptr num (n : lab) (n + 1)
  | otherwise = error "Cases are exhaustive"

-- Generates a structurally valid instruction
ainstr ∷ (MonadGen f, IMemC i) ⇒ Flags → Int → (State i m) → f Instr
ainstr f hltWeight st@State{..} =
  let (dptr, cptr, num, lab) =
        groupRegisters
          (imLength imem)
          (unRegSet regs)
          []
          []
          []
          []
          0
      genRegPtr = range' 0 (length (unRegSet regs) - 1)
      ifNaive x y = if genInstrDist f == Naive then y else x
      hltW = if testProp f == TestEENI || testProp f == TestEENI_Weak then hltWeight else 0
   in frequency $
        [ (5, pure Noop)
        , (hltW, pure Halt)
        , (10, liftM PcLab genRegPtr)
        , (10, liftG2 Lab genRegPtr genRegPtr)
        ]
          ++ [(10, liftG2 MLab (element dptr) genRegPtr) | not $ null dptr]
          ++ [(10, liftG2 PutLab (genLabelBelow H) genRegPtr)]
          ++ [ (10, liftG3 BCall (element cptr) (element lab) genRegPtr)
             | not $ null lab || null cptr
             ]
          ++ [(ifNaive 20 10, pure BRet) | not $ null $ unStack stack]
          ++ [ (ifNaive 13 10, liftG3 Alloc (element num) (element lab) genRegPtr)
             | not $ null num || null lab
             ]
          ++ [ (ifNaive 13 10, liftG2 Load (element dptr) genRegPtr)
             | not $ null dptr
             ]
          ++ [ (ifNaive 30 10, liftG2 Store (element dptr) genRegPtr)
             | not $ null dptr
             ]
          ++ [ (ifNaive 30 10, liftG2 Write (element dptr) genRegPtr)
             | not $ null dptr
             ]
          ++ [ (ifNaive 30 10, liftG2 Upgrade (element dptr) (element lab))
             | not $ null dptr || null lab
             ]
          ++ [(10, liftM Jump (element cptr)) | not $ null cptr]
          ++ [ (10, liftG2 Bnz (range' (-1) 2) (element num))
             | not $ null num
             ]
          ++ [ (10, liftG3 PSetOff (element dptr) (element num) genRegPtr)
             | not $ null dptr || null num
             ]
          ++ [(10, liftG2 Put int genRegPtr)]
          ++ [ (10, liftG4 BinOp arbitrary (element num) (element num) genRegPtr)
             | not $ null num
             ]
          ++ [(10, liftG2 MSize (element dptr) genRegPtr) | not $ null dptr]
          ++ [ (10, liftG2 PGetOff (element dptr) genRegPtr)
             | not $ null dptr
             ]
          ++ [(10, liftG2 Mov genRegPtr genRegPtr)]

popInstrSSNI ∷ (MonadGen f, IMemC i) ⇒ Flags → (State i m) → f (State i m)
popInstrSSNI f s@State{..} = do
  imem' ← ainstr f 0 s >>= return . fromInstrList . replicate (imLength imem)
  return s{imem = imem'}

copyInstructions ∷ (IMemC i) ⇒ [Maybe Instr] → (State i m) → (State i m)
copyInstructions z s = s{imem = fromInstrList $ map (fromMaybe Noop) z}

genExecHelper ∷
  (MonadGen f, IMemC i, MemC m Atom) ⇒
  Flags →
  RuleTable →
  State i m →
  State i m →
  Int →
  Int →
  Zipper (Maybe Instr) →
  f (State i m)
genExecHelper f _ s0 s 0 _ z = return $ copyInstructions (toList z) s0
genExecHelper f table s0 s tries hltWeight zipper = do
  (zipper', i) ← case current zipper of
    Nothing → do
      -- No instruction. Generate
      i ← label 0 (ainstr f hltWeight s)
      return (zipper{current = Just i}, i)
    Just i → return (zipper, i)
  case exec' table s i of
    Just s' →
      --       traceShow ("Executed", s ,s') $
      let (PAtm addr _) = (pc s')
       in case moveZipper zipper' addr of
            Just zipper'' →
              label 1 (genExecHelper f table s0 s' (tries - 1) (hltWeight + 1) zipper'')
            Nothing →
              -- PC out of bounds. End generation
              return $ copyInstructions (toList zipper') s0
    Nothing → return $ copyInstructions (toList zipper') s0

-- Naive-inefficient way of doing genByExec
genExecHelperLst ∷
  (MonadGen f, IMemC i, MemC m Atom) ⇒
  Flags →
  RuleTable →
  State i m →
  State i m →
  Int →
  [Maybe Instr] →
  f (State i m)
genExecHelperLst f _ s0 s 0 instrs = return $ copyInstructions instrs s0
genExecHelperLst f table s0 s tries instrs = do
  let (PAtm idx _) = pc s
  (instrs', i) ← case instrs !! idx of
    Nothing → do
      -- No instruction. Generate
      i ← label 0 (ainstr f 0 s)
      return $ (fromJust $ update idx (Just i) instrs, i)
    Just i → return (instrs, i)
  case exec table (copyInstructions instrs' s) of
    Just s' →
      let (PAtm addr _) = (pc s')
       in if addr < 0 || addr >= length instrs'
            then
              -- PC out of bounds. End generation
              return $ copyInstructions instrs' s0
            else label 1 (genExecHelperLst f table s0 s' (tries - 1) instrs')
    Nothing → return $ copyInstructions instrs s0

popInstrLLNI ∷
  (MonadGen f, IMemC i, MemC m Atom, Show i, Show m) ⇒
  Flags →
  RuleTable →
  State i m →
  f (State i m)
popInstrLLNI f table s@State{..} = do
  let len = imLength imem
  case memType f of
    MemList →
      label 0 (genExecHelperLst f table s s (3 * len) (replicate len Nothing))
    MemMap →
      label 1 (genExecHelper f table s s (3 * len) 0 (fromList $ replicate len Nothing))

popInstr ∷ (MonadGen f, Show i, Show m, IMemC i, MemC m Atom) ⇒ Flags → (State i m) → f (State i m)
popInstr f@Flags{..} s =
  case strategy of
    GenSSNI → label 0 (popInstrSSNI f s)
    GenByExec → label 1 (popInstrLLNI f defaultTable s)

------------------------- VARIATIONS --------------------------

class SmartVary a where
  smartVary ∷ (MonadGen f) ⇒ Label → Info → a → f a

instance SmartVary Value where
  smartVary _ info (VInt _) = label 0 (liftM VInt $ smartGen info)
  smartVary _ info (VPtr p) = label 1 (liftM VPtr $ smartGen info)
  -- CH: even if we don't have VCpt any more, could still try to turn
  -- valid code pointers more often into other code pointers
  --    smartVary _ info (VCpt p) = liftM VCpt $ choose (0, codeLen info - 1)
  smartVary _ info (VLab p) = label 2 (liftM VLab $ smartGen info)

instance SmartVary Atom where
  smartVary obs info a@(Atom v l)
    | l `flowsTo` obs = pure a
    | otherwise = liftG2 Atom (smartVary obs info v) (pure l)

-- Varying a high pc's label needs to be higher than obs!
instance SmartVary PtrAtom where
  smartVary obs info pc@(PAtm _ lpc)
    | isLow lpc obs = pure pc
    | otherwise = do
        PAtm addr' _' ← label 0 (smartGen info)
        lpc' ← label 1 (genLabelBetweenStrict obs H)
        return $ PAtm addr' lpc'

instance (SmartGen a, SmartVary a) ⇒ SmartVary (Frame a) where
  smartVary obs info f@(Frame stamp label' atoms)
    | isHigh stamp obs =
        label 0 (liftG2 (Frame stamp) (smartGen info) genData)
    | isHigh (stamp `lub` label') obs =
        label 1 (liftM (Frame stamp label') genData)
    | otherwise =
        label 2 (liftM (Frame stamp label') $ mapG (smartVary obs info) atoms)
   where
    len = length atoms
    genData = do
      dataLength' ← label 0 (range' len (len + 1))
      label 1 (replicateG dataLength' $ smartGen info)

varySingleFrame ∷
  (MonadGen f, MemC m Atom) ⇒
  Label →
  Info →
  m →
  Block →
  f m
varySingleFrame obs info mem block =
  case getFrame mem block of
    Just f → do
      f' ← smartVary obs info f
      case updFrame mem block f' of
        Just mem' → pure mem'
        Nothing → error "varySingleFrame Failed"
    Nothing → error "varySingleFrame Failed"

instance SmartVary (Mem Atom) where
  smartVary obs info mem =
    foldG (varySingleFrame obs info) mem (getBlocksBelow H mem)

instance (SmartVary a) ⇒ SmartVary [a] where
  smartVary obs info = mapG (smartVary obs info)

instance SmartVary RegSet where
  smartVary obs info (RegSet rs) =
    fmap RegSet $ smartVary obs info rs

instance SmartVary StkElt where
  smartVary obs info (StkElt (pc, lab, rs, r))
    | isLow (pcLab pc) obs =
        label 0 (fmap (StkElt . (pc,lab,,r)) $ smartVary obs info rs)
    | otherwise = label 1 do
        PAtm addr _ ← label 0 (smartGen info)
        pcl ← label 1 (genLabelBetweenStrict obs H)
        lab' ← label 2 (smartGen info)
        rs' ← label 3 (smartGen info)
        r' ← label 4 (smartGen info)
        return (StkElt ((PAtm addr pcl), lab', rs', r'))

-- Not complete! Extra high stack locations created in vary State if possible
instance SmartVary Stack where
  smartVary obs info (Stack s) =
    fmap Stack $ smartVary obs info s

-- Vary state
instance (MemC m Atom, IMemC i, SmartVary m) ⇒ SmartVary (State i m) where
  smartVary obs info s@State{..}
    | isLow (pcLab pc) obs = label 0 do
        regs' ← label 0 (smartVary obs info regs)
        mem' ← label 1 (smartVary obs info mem)
        stack' ← label 2 (smartVary obs info stack)
        return $ s{regs = regs', mem = mem', stack = stack'}
    | otherwise = label 1 do
        pc' ← label 0 (smartVary obs info pc)
        mem' ← label 1 (smartVary obs info mem)
        -- Need to vary stack length here!
        stack' ← label 2 (smartVary obs info stack)
        regs' ← label 3 (smartGen info)
        return $ s{regs = regs', mem = mem', stack = stack', pc = pc'}

-- Some constants, to be tweaked with Flaggy later on
data Parameters = Parameters
  { minFrames ∷ Int
  , maxFrames ∷ Int
  , minFrameSize ∷ Int
  , maxFrameSize ∷ Int
  , minCodeSize ∷ Int
  , maxCodeSize ∷ Int
  , noRegisters ∷ Int
  }

getParameters ∷ Flags → Parameters
getParameters Flags{..} =
  case strategy of
    GenSSNI → Parameters 2 2 2 2 2 noSteps 10
    GenByExec → Parameters 2 4 2 8 5 noSteps 10

-- Stamps start out bottom. Fill them up later!
genInitMem ∷ (MonadGen f, MemC m Atom) ⇒ Flags → f (m, [(Block, Int)])
genInitMem flags = do
  let Parameters{..} = getParameters flags
      aux 0 ml = return ml
      aux n (m, l) = do
        frameSize ← label 0 (range' minFrameSize maxFrameSize)
        label' ← label 1 (genLabelBelow H)
        let Just (block, m') = alloc frameSize label' bot (Atom (VInt 0) bot) m -- Assume frameSize > 0
        label 2 (aux (n - 1) (m', (block, frameSize - n) : l))
  noFrames ← label 0 (range' minFrames maxFrames)
  label 1 (aux noFrames (Memory.empty, []))

populateFrame ∷ (MonadGen f, MemC m Atom) ⇒ Info → m → Block → f m
populateFrame info mem block =
  case getFrame mem block of
    Just (Frame stamp label atoms) → do
      atoms' ← replicateG (length atoms) (smartGen info)
      case updFrame mem block (Frame stamp label atoms') of
        Just mem' → return mem'
        Nothing → error "populate Failed"
    Nothing → error "populate Failed"

populateMemory ∷ (MonadGen f, MemC m Atom) ⇒ Info → m → f m
populateMemory info mem =
  foldG (populateFrame info) mem (getBlocksBelow H mem)

-- LL: Add stamp instantiation - was unneeded in Coq? Suspicious...
instantiateStamps ∷ (MonadGen f) ⇒ (State i m) → f (State i m)
instantiateStamps = return

-- defaultFlags :: Flags
-- defaultFlags = Flags.defaultFlags

genEmptyState ∷
  (MonadGen f, MemC m Atom, IMemC i, SmartVary m, Show i, Show m) ⇒
  Flags →
  f (Variation (State i m))
genEmptyState flags = do
  let Parameters{..} = getParameters flags
      (mem, dfs) = (Memory.empty, [])
  codeSize ← label 0 (range minCodeSize maxCodeSize)
  let imem = fromInstrList $ replicate codeSize Noop
      info = MkInfo flags codeSize dfs noRegisters
      pc = PAtm 0 L
      stack = Stack []
  regs ← label 1 (smartGen info)
  let state0 = State{..}
  st ← label 2 (popInstr flags state0)
  obs ← label 3 (genLabelBetweenLax L H) -- in case we change to arbitrary number
  st' ← label 4 (smartVary obs info st)
  {- traceShow (Var obs st st') $ -}
  return $ Var obs st st'

initPc ∷ (MonadGen f) ⇒ Info → f PtrAtom
initPc info@(MkInfo Flags{..} cl _ _) = do
  case strategy of
    GenByExec → label 0 (liftM (PAtm 0) (smartGen info))
    GenSSNI → label 1 (liftG2 PAtm (range' 0 (cl - 1)) (smartGen info))

genVariationState ∷
  (MonadGen f, MemC m Atom, IMemC i, SmartVary m, Show i, Show m) ⇒
  Flags →
  f (Variation (State i m))
genVariationState flags = do
  let Parameters{..} = getParameters flags
  (initMem, dfs) ← label 0 (genInitMem flags)
  codeSize ← label 1 (range' minCodeSize maxCodeSize)
  let imem = fromInstrList $ replicate codeSize Noop
      info = MkInfo flags codeSize dfs noRegisters
  pc ← label 2 (initPc info)
  regs ← label 3 (smartGen info)
  stack ← label 4 (smartGenStack pc info)
  mem ← label 5 (populateMemory info initMem)
  let state0 = State{..}
  state1 ← label 6 (popInstr flags state0)
  st ← label 7 (instantiateStamps state1)
  obs ← label 8 (genLabelBetweenLax L H) -- in case we change to arbitrary number
  st' ← label 9 (smartVary obs info st)
  return $ Var obs st st'
