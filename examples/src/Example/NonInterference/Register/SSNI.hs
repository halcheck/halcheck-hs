{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant if" #-}

module Example.NonInterference.Register.SSNI where

import Example.NonInterference.Register.Indist
import Example.NonInterference.Register.Instructions
import Example.NonInterference.Register.Labels
import Example.NonInterference.Register.Machine
import Example.NonInterference.Register.Memory
import Example.NonInterference.Register.Primitives
import Example.NonInterference.Register.Rules

propSSNI ∷
  (MemC m Atom, IMemC i, Indist m, Indist i) ⇒
  RuleTable →
  Variation (State i m) →
  Bool
propSSNI t (Var obs st1 st2) =
  let isLowState st = isLow (pcLab $ pc st) obs
   in if indist obs st1 st2
        then case exec t st1 of
          Just st1' →
            if isLowState st1
              then case exec t st2 of
                Just st2' →
                  -- Both took a low step
                  {-                        whenFail (putStrLn $ PP.render
                                                   $ text "Low Step\nStarting State:\n" $$
                                                     pp v $$
                                                     text "Ending State:\n" $$
                                                     pp (Var obs st1' st2')) $ -}
                  indist obs st1' st2'
                Nothing →
                  -- 1 took a low step and 2 failed
                  False
              else -- st1 is High
                if isLowState st1'
                  then case exec t st2 of
                    Just st2' →
                      if isLowState st2'
                        then
                          -- High -> low
                          {-                              whenFail (PP.render
                                                           $ text "Low Step\nStarting State:\n" $$
                                                             pp v $$
                                                             text "Ending State:\n" $$
                                                             pp (Var obs st1' st2')) $
                          -}
                          indist obs st1' st2'
                        else -- 1 High -> Low, 2 -> High -> High. Check 2
                          indist obs st2 st2'
                    Nothing →
                      -- 1 High -> Low, two failed. Reject
                      False
                  else -- 1: High -> High
                  {-                    whenFail (putStrLn $ PP.render
                                                $ text "HighStep:\n" $$
                                                  pp (Var obs st1 st1') $$
                                                  (text . show $ indist obs st1 st1')
                                               ) $ -}
                    indist obs st1 st1'
          Nothing → False -- 1 Failed
        else -- not indistinguishable!
          False
