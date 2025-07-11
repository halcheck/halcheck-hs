{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Redundant $" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

{-# HLINT ignore "Use mapMaybe" #-}

module Example.NonInterference.Register.Indist where

import Data.Maybe

import Example.NonInterference.Register.Instructions
import Example.NonInterference.Register.Labels
import Example.NonInterference.Register.Machine
import Example.NonInterference.Register.Memory
import Example.NonInterference.Register.Primitives

-- Indistinguishability type class
class Indist a where
  indist ∷ Label → a → a → Bool

instance Indist Instr where
  indist = const (==)

instance Indist Label where
  indist = const (==)

instance Indist Int where
  indist = const (==)

-- Value indistinguishability

-- * For pointers, it is syntactic equality because of the per-level allocator
instance Indist Value where
  indist = const (==)

-- Atom indistinguishability

-- * Equal Labels (public labels)

-- ** Low Labels  -> Indist Values

-- ** High Labels -> True
instance Indist Atom where
  indist obs (Atom v1 l1) (Atom v2 l2)
    | l1 /= l2 = False
    | l1 `flowsTo` obs = indist obs v1 v2
    | otherwise = True

-- PC indistinguishability

-- * Both High -> Ok

-- * At least one PC low -> syntactic equality

-- ! The pc protects it's own label !
instance Indist PtrAtom where
  indist obs (PAtm i1 l1) (PAtm i2 l2)
    | isLow l1 obs || isLow l2 obs =
        l1 == l2 && i1 == i2
    | otherwise = True

-- List Indistinguishability
instance (Indist a) ⇒ Indist [a] where
  indist obs [] [] = True
  indist obs (x : xs) (y : ys) = indist obs x y && indist obs xs ys
  indist _ _ _ = False

-- RegSet Indistinguishability
instance Indist RegSet where
  indist obs (RegSet as) (RegSet as') = indist obs as as'

-- Frame Indistinguishability

-- * If both stamps are low

--   + Equal labels
--   + Low Labels -> Indistinguishable data

-- * Otherwise both need to be high

-- * LL: Unclear : One high, one low?

-- CH: TODO: this is obsolete, remove stamps from frames and match new
--     definition of memory indistinguishability
instance (Indist a) ⇒ Indist (Frame a) where
  indist obs (Frame s1 l1 as1) (Frame s2 l2 as2)
    | isLow s1 obs || isLow s2 obs =
        l1 == l2
          && ( if isLow l1 obs
                then indist obs as1 as2
                else True
             )
    | otherwise = True

-- Memory Indistinguishability

-- * Get all memory frames with stamps below the obs level, in the same order

-- * Ensure they are pairwise indistinguishable
instance Indist (Mem Atom) where
  indist obs m1 m2 = indist obs (getFrames m1) (getFrames m2)
   where
    getFrames m = catMaybes $ map (getFrame m) (getBlocksBelow obs m)

-- Cropping the high part of the stack

isLowStkElt ∷ Label → StkElt → Bool
isLowStkElt obs (StkElt (pc, _, _, _)) = isLow (pcLab pc) obs

cropTop ∷ Label → Stack → Stack
cropTop _ (Stack []) = Stack []
cropTop obs s@(Stack (StkElt (pc, _, _, _) : s')) =
  if isLow (pcLab pc) obs then s else cropTop obs $ Stack s'

-- Indistinghuishability of stack elements
instance Indist StkElt where
  indist obs s1@(StkElt (pc1, l1, rs1, r1)) s2@(StkElt (pc2, l2, rs2, r2)) =
    debug (show ("When comparing", s1, s2)) $
      if isLow (pcLab pc1) obs || isLow (pcLab pc2) obs
        then
          indist obs pc1 pc2 -- CH: just equality, why not call that?
            && indist obs l1 l2 -- CH: just equality, why not call that?
            && indist obs rs1 rs2
            && indist obs r1 r2 -- CH: just equality, why not call that?
        else True

indistStack ∷ PtrAtom → PtrAtom → Label → Stack → Stack → Bool
indistStack (PAtm _ pcl1) (PAtm _ pcl2) obs s1 s2 =
  let s1' = (unStack $ (if isHigh pcl1 obs then cropTop obs s1 else s1))
      s2' = (unStack $ (if isHigh pcl2 obs then cropTop obs s2 else s2))
   in debug (show $ ("Cropped", s1', s2')) $ indist obs s1' s2'

-- State indistinguishability

-- * memories, instruction memories and stacks must always be indistinguishable

-- * if one of the pcs labeled low then the pcs and registers must be

--   indistinguishable too
debug ∷ String → Bool → Bool
-- debug s x = if not x then unsafePerformIO $ do putStrLn s >> return x else x
debug s x = x

instance (IMemC i, MemC m Atom, Indist m, Indist i) ⇒ Indist (State i m) where
  indist obs (State imem1 mem1 s1 regs1 pc1) (State imem2 mem2 s2 regs2 pc2) =
    debug "IMemory" (indist obs imem1 imem2)
      && debug "Memory" (indist obs mem1 mem2)
      && debug "Stack" (indistStack pc1 pc2 obs s1 s2)
      && if isLow (pcLab pc1) obs || isLow (pcLab pc2) obs
        then
          indist obs pc1 pc2
            && debug "Registers" (indist obs regs1 regs2)
        else True
