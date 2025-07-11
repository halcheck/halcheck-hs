{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use =<<" #-}
{-# HLINT ignore "Redundant bracket" #-}

module Example.NonInterference.Register.Rules where

import Data.Maybe

import Example.NonInterference.Register.Instructions
import Example.NonInterference.Register.Labels

import Control.DeepSeq (NFData)
import Control.Monad (join)
import Data.Map (Map)
import qualified Data.Map as Map
import GHC.Generics (Generic)

data MVec = MVec
  { mLab1 ∷ Label
  , mLab2 ∷ Label
  , mLab3 ∷ Label
  , mLab4 ∷ Label
  , mLab5 ∷ Label
  , mLabPC ∷ Label
  }
  deriving (Generic, NFData)

type Var = MVec → Label

data RuleExpr
  = EBot
  | EVar (String, Var)
  | EJoin RuleExpr RuleExpr
  deriving (Generic, NFData)

instance Show RuleExpr where
  show EBot = "EBot"
  show (EVar (s, _)) = "EVar " ++ s
  show (EJoin e1 e2) = "JOIN ( " ++ show e1 ++ " " ++ show e2 ++ " )"

data SideCond
  = ATrue
  | ALe RuleExpr RuleExpr
  | AAnd SideCond SideCond
  | AOr SideCond SideCond
  deriving (Generic, NFData, Show)

data Rule = Rule
  { allow ∷ SideCond
  , rlab ∷ Maybe RuleExpr
  , rlpc ∷ RuleExpr
  }
  deriving (Generic, NFData, Show)

type RVec = Maybe (Maybe Label, Label)

evalExpr ∷ MVec → RuleExpr → Label
evalExpr _ EBot = bot
evalExpr m (EVar (_, l)) = l m
evalExpr m (EJoin r1 r2) = evalExpr m r1 `lub` evalExpr m r2

evalCond ∷ MVec → SideCond → Bool
evalCond _m ATrue = True
evalCond m (AAnd c1 c2) = evalCond m c1 && evalCond m c2
evalCond m (AOr c1 c2) = evalCond m c1 || evalCond m c2
evalCond m (ALe e1 e2) = evalExpr m e1 `flowsTo` evalExpr m e2

applyRule ∷ MVec → Rule → RVec
applyRule m Rule{..}
  | evalCond m allow = Just (fmap (evalExpr m) rlab, evalExpr m rlpc)
  | otherwise = Nothing

type RuleTable = Map InstrKind Rule

getRule ∷ RuleTable → InstrKind → Rule
getRule t op = fromJust $ Map.lookup op t

runTMU' ∷ RuleTable → InstrKind → MVec → RVec
runTMU' t op m = join . fmap (applyRule m) $ Map.lookup op t

runTMU ∷ RuleTable → InstrKind → [Label] → Label → RVec
runTMU t op labs lpc = runTMU' t op (buildMVec (labs ++ repeat undefined) lpc)

buildMVec ∷ [Label] → Label → MVec
buildMVec (l1 : l2 : l3 : l4 : l5 : _) lpc = MVec l1 l2 l3 l4 l5 lpc
buildMVec _ _ = error "buildMVec"

-- Default Rule Table

parseRule ∷ String → (InstrKind, Rule)
parseRule s =
  let (op : _ : _ : rest) = words s
      (scond, (_ : rest')) = span (/= ",") rest
      (rexp1, (_ : rexp2)) = span (/= ",") rest'
   in ( read op
      , Rule
          (fst $ parseSCond scond)
          (fst $ parseExpr rexp1)
          (fromJust . fst $ parseExpr rexp2)
      )

parseSCond ∷ [String] → (SideCond, [String])
parseSCond ("TRUE" : r) = (ATrue, r)
parseSCond ("LE" : r) =
  let (Just e1, r') = parseExpr r
      (Just e2, r'') = parseExpr r'
   in (ALe e1 e2, r'')
parseSCond ("AND" : r) =
  let (c1, r') = parseSCond r
      (c2, r'') = parseSCond r'
   in (AAnd c1 c2, r'')
parseSCond ("(" : r) = parseSCond r
parseSCond (")" : r) = parseSCond r
parseSCond a = error $ "Unexpected" ++ show a

parseExpr ∷ [String] → (Maybe RuleExpr, [String])
parseExpr ("__" : r) = (Nothing, r)
parseExpr ("(" : r) = parseExpr r
parseExpr (")" : r) = parseExpr r
parseExpr ("BOT" : r) = (Just EBot, r)
parseExpr ("JOIN" : r) =
  let (Just e1, r') = parseExpr r
      (Just e2, r'') = parseExpr r'
   in (Just $ EJoin e1 e2, r'')
parseExpr ("Lab1" : r) = (Just $ EVar ("Lab1", mLab1), r)
parseExpr ("Lab2" : r) = (Just $ EVar ("Lab2", mLab2), r)
parseExpr ("Lab3" : r) = (Just $ EVar ("Lab3", mLab3), r)
parseExpr ("Lab4" : r) = (Just $ EVar ("Lab4", mLab4), r)
parseExpr ("Lab5" : r) = (Just $ EVar ("Lab5", mLab5), r)
parseExpr ("LabPC" : r) = (Just $ EVar ("LabPC", mLabPC), r)
parseExpr a = error $ "Unexpected" ++ show a

defaultTable ∷ RuleTable
defaultTable =
  Map.fromList . map parseRule $
    [ "PUT     ::=  << TRUE , BOT , LabPC >>"
    , "MOV     ::=  << TRUE , Lab1 , LabPC >>"
    , "LOAD    ::=  << TRUE , Lab3 , JOIN LabPC ( JOIN Lab1 Lab2 ) >>"
    , "STORE   ::=  << LE ( JOIN Lab1 LabPC ) Lab2 , Lab3 , LabPC >>"
    , "BINOP   ::=  << TRUE , JOIN Lab1 Lab2 , LabPC >>"
    , "NOOP    ::=  << TRUE , __ , LabPC >>"
    , "JUMP    ::=  << TRUE , __ , JOIN LabPC Lab1 >>"
    , "BNZ     ::=  << TRUE , __ , JOIN Lab1 LabPC >>"
    , "BCALL   ::=  << TRUE , JOIN Lab2 LabPC , JOIN Lab1 LabPC >>"
    , "BRET    ::=  << LE ( JOIN Lab1 LabPC ) ( JOIN Lab2 Lab3 ) , Lab2 , Lab3 >>"
    , "PUTLAB  ::=  << TRUE , BOT , LabPC >>"
    , "LAB     ::=  << TRUE , BOT , LabPC >>"
    , "PCLAB   ::=  << TRUE , BOT , LabPC >>"
    , "ALLOC   ::=  << TRUE , JOIN Lab1 Lab2 , LabPC >>"
    , "WRITE   ::=  << LE ( JOIN ( JOIN LabPC Lab1 ) Lab3 ) ( JOIN Lab2 Lab4 ) , Lab4 , LabPC >>"
    , -- I think I can get this with more complex encoding
      "UPGRADE  ::=  << AND ( LE Lab3 ( JOIN Lab4 Lab2 ) ) ( LE ( JOIN ( JOIN LabPC Lab5 ) Lab1 ) Lab2 ) , Lab4 , LabPC >>"
    , -- Simpler encoding gives us this already
      --  "UPGRADE  ::=  << AND ( LE ( JOIN Lab3 ( JOIN Lab1 Lab2 ) ) ( JOIN Lab4 ( JOIN LabPC Lab5 ) ) ) ( LE ( JOIN ( JOIN LabPC Lab5 ) Lab1 ) Lab2 ) , Lab4 , LabPC >>",
      "PSETOFF ::=  << TRUE , JOIN Lab1 Lab2 , LabPC >>"
    , "PGETOFF ::=  << TRUE , Lab1 , LabPC >>"
    , "MSIZE   ::=  << TRUE , Lab2 , JOIN LabPC Lab1 >>"
    , "MLAB    ::=  << TRUE , Lab1 , LabPC >>"
    ]
