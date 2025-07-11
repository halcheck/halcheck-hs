{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# HLINT ignore "Use :" #-}
{-# HLINT ignore "Redundant <$>" #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Example.NonInterference.Stack.ObservableInst where

import Control.Monad
import Control.Monad.Gen (frequency, oneof, label, mapG, liftG2)

import Data.List ((\\))

import Example.NonInterference.Stack.Flags
import Example.NonInterference.Stack.Instr
import Example.NonInterference.Stack.Labels
import Example.NonInterference.Stack.Observable

import Example.NonInterference.Stack.Util

import Data.Vector.Internal.Check (HasCallStack)
import Example.NonInterference.Stack.Generation
import Example.NonInterference.Stack.Machine

instance (Flaggy DynFlags) ⇒ Arbitrary AS where
  arbitrary = genAS vary
  shrinks as = filter (/= as) . map (\(Variation as' _) → as') . shrinkV $ join Variation as

{- In this module we define and experiment with shrinking
 - Variations of Abstract Machines -}

isLowRet ∷ AStkElt → Bool
isLowRet (ARet (Labeled L _)) = True
isLowRet _ = False

cropTop ∷ [AStkElt] → [AStkElt]
cropTop [] = []
cropTop (h : t) | isLowRet h = h : t
cropTop (_ : t) = cropTop t

instance (Flaggy DynFlags) ⇒ Observable AS where
  as ~~~ as' =
    lab (apc as) == lab (apc as')
      && case equiv getFlags of
        EquivMem → pcIs L --> equivImems && equivMems
        EquivLow → pcIs L --> equivImems && equivMems && equivPcs && equivStks id
        EquivWrongFull → equivImems && equivMems && equivPcs && equivStks id
        EquivFull →
          equivImems
            && equivMems
            && equivPcs
            && equivStks (if pcIs L then id else cropTop)
   where
    pcIs l = lab (apc as) == l
    equivImems = aimem as ~~~ aimem as'
    equivPcs = apc as ~~~ apc as'
    equivMems = amem as ~~~ amem as'
    equivStks f = f (astk as) ~~~ f (astk as')

  vary as =
    case equiv getFlags of
      EquivMem →
        if pcIs L
          then do
            aimem ← label 0 (varyImem $ aimem as)
            amem ← label 1 (varyMem $ amem as)
            astk ←
              if starting_as getFlags == StartInitial
                then return []
                else label 2 arbitrary -- CH: XXX: this does no smart ints!
            apc ← return $ apc as
            return AS{..}
          else do
            as' ← label 3 arbitrary
            return as'{apc = apc as' `withLab` H}
      EquivLow →
        if pcIs L
          then do
            aimem ← label 4 $ varyImem $ aimem as
            amem ← label 5 $ varyMem $ amem as
            astk ← label 6 $ varyStack $ astk as
            apc ← return $ apc as
            return AS{..}
          else do
            as' ← label 7 arbitrary
            return as'{apc = apc as' `withLab` H}
      EquivWrongFull → do
        aimem ← label 8 $ varyImem $ aimem as
        amem ← label 9 $ varyMem $ amem as
        astk ← label 10 $ varyStack $ astk as
        apc ← label 11 $ varyAtom $ apc as
        -- we could do a bit better by
        -- choosing just valid addresses
        return AS{..}
      EquivFull → do
        aimem ← label 12 $ varyImem $ aimem as
        amem ← label 13 $ varyMem $ amem as
        astk ←
          if pcIs L
            then label 14 $ varyStack $ astk as
            else do
              l ← label 15 $ arbitrary
              let stackTop = filter (not . isLowRet) l
              stackRest ← label 16 $ varyStack $ cropTop $ astk as
              return $ stackTop ++ stackRest
        apc ← label 17 $ varyAtom $ apc as -- ditto
        return AS{..}
   where
    pcIs l = lab (apc as) == l

    varyInt i
      | smart_ints getFlags =
          frequency $
            [ (10, length (amem as) `upfrom` 0)
            | i `isIndex` amem as
            ]
              ++ [ (10, length (aimem as) `upfrom` 0)
                 | i `isIndex` aimem as && is_not_basic
                 ]
              ++ [(1, int)]
      | otherwise =
          int

    is_not_basic = gen_instrs getFlags /= InstrsBasic

    varyAtom _a@(Labeled H i) =
      case atom_equiv getFlags of
        LabelsObservable → Labeled H <$> varyInt i
        LabelsNotObservable →
          oneof
            [ Labeled H <$> varyInt i
            , return $ Labeled L i
            ]
        HighEquivEverything → labeled sint
    varyAtom a@(Labeled L i) =
      case atom_equiv getFlags of
        LabelsObservable → return a
        LabelsNotObservable →
          oneof
            [ return a
            , return $ Labeled H i
            ]
        HighEquivEverything →
          oneof
            [ return a
            , Labeled H <$> sint
            ]

    sint = smartInt (length (aimem as)) (length (amem as))

    varyStkElt (AData a@(Labeled L _)) = AData <$> pure a
    varyStkElt (AData (Labeled H i)) =
      oneof $
        [AData . Labeled H <$> varyInt i]
          ++ [ ARet . Labeled H <$> liftG2 (,) sint arbitrary
             | stk_elt_equiv getFlags == LabelOnTop
             ]
    varyStkElt (ARet a@(Labeled L _)) = ARet <$> pure a
    varyStkElt (ARet (Labeled H (i, r))) =
      oneof $
        [ARet . Labeled H <$> liftG2 (,) (varyInt i) (vary r)]
          ++ [AData . Labeled H <$> sint | stk_elt_equiv getFlags == LabelOnTop]

    varyInstr (Push a) = Push <$> varyAtom a
    varyInstr i = pure i

    varyMem =
      if starting_as getFlags == StartInitial
        then return
        else mapG varyAtom
    varyImem = mapG varyInstr
    varyStack =
      if starting_as getFlags == StartInitial
        then const $ return []
        else mapG varyStkElt

  shrinkV _ | shrink_nothing getFlags = []
  shrinkV (Variation as as') =
    shrinkV' (Variation as as')
      ++ if shrinkNoops
        then
          [ v' | (Noop, Noop, i) ← zip3 (aimem as) (aimem as') [0 ..], let v =
                                                                            Variation
                                                                              as{aimem = take i (aimem as) ++ drop (i + 1) (aimem as)}
                                                                              as'{aimem = take i (aimem as') ++ drop (i + 1) (aimem as')}, v' ← v : shrinkV' v
          ]
        else []
   where
    shrinkNoops = shrink_noops getFlags
    shrinkV' (Variation as as') =
      easy_shrink ++ (harder_shrink \\ easy_shrink)
     where
      which_equiv = equiv getFlags
      easy_shrink -- applies to all equivalences
        =
        [ Variation as{aimem = init (aimem as)} as'{aimem = init (aimem as')}
        | length (aimem as) > 1
        , length (aimem as') > 1
        ]
          ++ [ Variation as{amem = init (amem as)} as'{amem = init (amem as')}
             | amem as /= []
             , amem as' /= []
             ]

      harder_shrink
        | L == lab (apc as) && (which_equiv == EquivMem) =
            [ Variation
              AS{amem = amem', aimem = aimem', astk = astk', apc = apc as}
              AS{amem = amem'', aimem = aimem'', astk = astk'', apc = apc as'}
            | ( Variation
                  (amem', ShrinkTailNonEmpty aimem')
                  (amem'', ShrinkTailNonEmpty aimem'')
                , astk'
                , astk''
                ) ←
                shrinks
                  ( Variation
                      (amem as, ShrinkTailNonEmpty $ aimem as)
                      (amem as', ShrinkTailNonEmpty $ aimem as')
                  , astk as
                  , astk as'
                  )
            ]
              ++
              -- try shrinking TWO instructions to Noop simultaneously
              [ Variation as{aimem = aimem'} as'{aimem = aimem''}
              | shrink_to_noop getFlags
              , (aimem', aimem'') ← shrink2noops (aimem as) (aimem as')
              ]
        | L == lab (apc as) || (which_equiv == EquivWrongFull) =
            [ Variation
              AS{amem = amem', aimem = aimem', astk = astk', apc = apc as}
              AS{amem = amem'', aimem = aimem'', astk = astk'', apc = apc as'}
            | not (null (aimem as))
            , Variation
                (amem', ShrinkTailNonEmpty aimem', astk')
                (amem'', ShrinkTailNonEmpty aimem'', astk'') ←
                shrinkV
                  ( Variation
                      (amem as, ShrinkTailNonEmpty $ aimem as, astk as)
                      (amem as', ShrinkTailNonEmpty $ aimem as', astk as')
                  )
            ]
        | EquivFull ← which_equiv =
            -- High PC, full equivalence means we can shrinks stacks cleverly
            [ Variation
              AS{amem = amem', aimem = aimem', astk = astk', apc = apc as}
              AS{amem = amem'', aimem = aimem'', astk = astk'', apc = apc as'}
            | Variation
                (amem', ShrinkTailNonEmpty aimem', SHS astk')
                (amem'', ShrinkTailNonEmpty aimem'', SHS astk'') ←
                shrinkV
                  ( Variation
                      (amem as, ShrinkTailNonEmpty (aimem as), SHS (astk as))
                      (amem as', ShrinkTailNonEmpty (aimem as'), SHS (astk as'))
                  )
            ]
        | otherwise =
            -- Just High PC and some other equivalence (EquivMem, or EquivLow)
            -- Is it worth shrinking in some other completely crazy way?
            [ Variation
              AS{amem = amem', aimem = aimem', astk = astk', apc = apc as}
              AS{amem = amem'', aimem = aimem'', astk = astk'', apc = apc as'}
            | ( astk'
                , astk''
                , (amem', ShrinkTailNonEmpty aimem')
                , (amem'', ShrinkTailNonEmpty aimem'')
                ) ←
                shrinks
                  ( astk as
                  , astk as'
                  , (amem as, ShrinkTailNonEmpty (aimem as))
                  , (amem as', ShrinkTailNonEmpty (aimem as'))
                  )
            ]

-- shrinks two instructions to Noop simultaneously
shrink2noops ∷ [Instr] → [Instr] → [([Instr], [Instr])]
shrink2noops aimem aimem'
  | length noops >= 2 =
      [ (replace i j aimem, replace i j aimem')
      | i ← noops
      , j ← noops
      , i < j
      ]
 where
  noops = [i | (instr, i) ← zip aimem [0 ..], instr /= Noop]
  replace i j aimem =
    [ if k == i || k == j then Noop else instr
    | (instr, k) ← zip aimem [0 ..]
    ]
shrink2noops _aimem _aimem' = []

{-
                     (if lab (apc as) == L
              then
                [ Variation AS{amem=amem', aimem=aimem', astk=astk', apc=apc as}
                            AS{amem=amem'', aimem=aimem'', astk=astk'', apc=apc as'}
                      | Variation (amem',ShrinkTailNonEmpty aimem',astk')
                                  (amem'',ShrinkTailNonEmpty aimem'',astk'') <-
                           shrinkV (Variation (amem as,ShrinkTailNonEmpty $ aimem as,astk as)
                                              (amem as',ShrinkTailNonEmpty $ aimem as',astk as')) ]
              else if equiv getFlags /= EquivFull
                   then -- high PC means only choice is to shrinks the
                        -- two stacks separately
                   [ Variation AS{amem=amem',  aimem=aimem',  astk=astk',  apc=apc as}
                               AS{amem=amem'', aimem=aimem'', astk=astk'', apc=apc as'}
                      |  (astk', astk'', Variation (amem', ShrinkTailNonEmpty aimem')
                                                   (amem'',ShrinkTailNonEmpty aimem'')) <-
                           shrinks (astk as, astk as',
                                   Variation (amem as,  ShrinkTailNonEmpty (aimem as))
                                             (amem as', ShrinkTailNonEmpty (aimem as'))) ]
                   else
                   [ Variation AS{amem=amem',  aimem=aimem',  astk=astk',  apc=apc as}
                               AS{amem=amem'', aimem=aimem'', astk=astk'', apc=apc as'}
                      | Variation (amem', ShrinkTailNonEmpty aimem',  SHS astk')
                                  (amem'',ShrinkTailNonEmpty aimem'', SHS astk'') <-
                           shrinkV (Variation (amem as,  ShrinkTailNonEmpty (aimem as),  SHS (astk as))
                                              (amem as', ShrinkTailNonEmpty (aimem as'), SHS (astk as')))]
            \\ easy)
 -}

-- Note that we don't shrinks the stack here: that results in a
-- bunch of Push instructions at the head of the program

newtype ShrinkHighStack = SHS [AStkElt] deriving (Show, Eq)

-- A stack that is a prefix of a stuck up to an isLowRet element

instance (Flaggy DynFlags) ⇒ Arbitrary ShrinkHighStack where
  arbitrary = SHS <$> arbitrary

instance (Flaggy DynFlags) ⇒ Observable ShrinkHighStack where
  (SHS as) ~~~ (SHS bs) = cropTop as ~~~ cropTop bs

  vary (SHS as) =
    do
      l ← arbitrary
      let top = filter (not . isLowRet) l
      bottom ← vary (cropTop as)
      return (SHS (top ++ bottom))

  shrinkV (Variation (SHS as) (SHS bs)) =
    let (asH, asL) = break isLowRet as
        (bsH, bsL) = break isLowRet bs
     in map (fmap SHS) $
          -- If we shrinks the label of a high return address to a low return
          -- address, then the lower portions of a stack can change
          -- independently, which is bad; hence, we filter those out.
          [Variation (asH' ++ asL) bs | asH' ← filter (not . any isLowRet) $ shrinks asH]
            ++ [Variation as (bsH' ++ bsL) | bsH' ← filter (not . any isLowRet) $ shrinks bsH]
            ++ [Variation (asH ++ asL') (bsH ++ bsL') | Variation asL' bsL' ← shrinkV $ Variation asL bsL]

newtype ShrinkTailNonEmpty a = ShrinkTailNonEmpty_ [a] deriving (Show, Eq)

pattern ShrinkTailNonEmpty ∷ (HasCallStack) ⇒ () ⇒ [a] → ShrinkTailNonEmpty a
pattern ShrinkTailNonEmpty xs ← ShrinkTailNonEmpty_ xs
  where
    ShrinkTailNonEmpty [] = error "ShrinkTailNonEmpty: empty list"
    ShrinkTailNonEmpty xs = ShrinkTailNonEmpty_ xs
{-# COMPLETE ShrinkTailNonEmpty #-}

instance (Arbitrary a) ⇒ Arbitrary (ShrinkTailNonEmpty a) where
  arbitrary = ShrinkTailNonEmpty <$> ((:) <$> arbitrary <*> arbitrary)
  shrinks (ShrinkTailNonEmpty xs) = do
    xs' ← shrinks xs
    case xs' of
      [] → []
      _ → pure (ShrinkTailNonEmpty xs')

instance (Show a, Observable a) ⇒ Observable (ShrinkTailNonEmpty a) where
  (ShrinkTailNonEmpty xs) ~~~ (ShrinkTailNonEmpty ys) = xs ~~~ ys
  vary (ShrinkTailNonEmpty as) =
    ShrinkTailNonEmpty <$> vary as
  shrinkV (Variation (ShrinkTailNonEmpty [_]) (ShrinkTailNonEmpty [_])) = []
  shrinkV (Variation (ShrinkTailNonEmpty (a : as)) (ShrinkTailNonEmpty (a' : as'))) =
    map (fmap ShrinkTailNonEmpty) $
      Variation (init (a : as)) (init (a' : as'))
        : [ Variation (a : vs) (a' : vs')
          | Variation (ShrinkTailNonEmpty vs) (ShrinkTailNonEmpty vs') ←
              shrinkV (Variation (ShrinkTailNonEmpty as) (ShrinkTailNonEmpty as'))
          ]
        ++ [ Variation (v : as) (v' : as')
           | Variation v v' ←
              shrinkV (Variation a a')
           ]
  shrinkV (Variation (ShrinkTailNonEmpty []) (ShrinkTailNonEmpty [])) =
    error "ShrinkTailNonEmpty should never hold empty lists (shrinkV)"
  shrinkV v = errorShrinkV "(ShrinkTailNonEmpty a)" v
