{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
-- |
-- Copyright   : (c) 2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Unit tests for the functions dealing with term algebra and related notions.
module Term.UnitTests -- (tests)
 where

import Term.Substitution
import Term.Subsumption
import Term.Builtin.Convenience
import Term.Unification
import Term.Rewriting.Norm
import Term.Narrowing.Variants
import Term.Positions

import Text.PrettyPrint.Class

import Data.List
import Data.Maybe
import qualified Data.Map as M
import Prelude
import Test.HUnit
import Control.Monad.Reader
-- import Data.Monoid

import Term.Homomorphism.LPETerm
import Term.Homomorphism.Unification

import Extension.Prelude (sortednub)

testEqual :: (Eq a, Show a) => String -> a -> a -> Test
testEqual t a b = TestLabel t $ TestCase $ assertEqual t b a

testTrue :: String -> Bool -> Test
testTrue t a = TestLabel t $ TestCase $ assertBool t a

-- *****************************************************************************
-- Tests for Matching
-- *****************************************************************************

testsMatching :: MaudeHandle -> Test
testsMatching hnd = TestLabel "Tests for Matching" $
    TestList
      [ testTrue "a" (propMatchSound hnd f1 f2)
      , testTrue "b" (propMatchSound hnd (pair (f1,inv (f2))) (pair (f1,inv (f2))))
      , testTrue "c" (propMatchSound hnd t1 t2)
      , testTrue "d" (propMatchSound hnd (x1 # f1) f1)
      , testTrue "e" $ null (solveMatchLNTerm (pair (x1,x2) `matchWith` pair (x1,x1)) `runReader` hnd)
      ]
  where
    t1 = expo (inv (pair (f1,f2)), f2 # (inv f2) # f3 # f4 # f2)
    t2 = expo (inv (pair (f1,f2)), f3 # (inv f2) # f2 # x1 # f5 # f2)

propMatchSound :: MaudeHandle -> LNTerm -> LNTerm -> Bool
propMatchSound mhnd t1 p = all (\s -> applyVTerm s t1 == applyVTerm s p) substs
  where substs = solveMatchLNTerm (t1 `matchWith` p) `runReader` mhnd



-- *****************************************************************************
-- Tests for Unification
-- *****************************************************************************

testsUnify :: MaudeHandle -> Test
testsUnify mhnd = TestLabel "Tests for Unify" $
    TestList
      [ testTrue "a" (propUnifySound mhnd (pair (f1,inv (f2))) (pair (f1,inv (f2))))
      , testTrue "b" (propUnifySound mhnd t1 t2)
      , testTrue "c" (propUnifySound mhnd u1 u2)
      , testTrue "d" (propUnifySound mhnd (sdec (x1,y1)) (sdec (senc (x2,x3), x4)))
      , testTrue "e" (propUnifySound mhnd (fAppEMap (p2,x1)) (fAppEMap (p1,x2)))
    ]
  where
    t1 = expo (inv (pair (f1,f2)), f2 *: (inv f2) *: f3 *: f4 *: x2)
    t2 = expo (inv (pair (f1,f2)), f3 *: (inv f2) *: f2 *: f4 *: f5 *: f2)
    u1 = (f2 *: (inv f2) *: f3 *: f4 *: x2)
    u2 = (f3 *: (inv f2) *: f2 *: f4 *: f5 *: f2)

propUnifySound :: MaudeHandle -> LNTerm -> LNTerm -> Bool
propUnifySound hnd t1 t2 = all (\s -> let s' = freshToFreeAvoiding s [t1,t2] in
                                  applyVTerm s' t1 == applyVTerm s' t2) substs
                               && not (null substs)
  where
    substs = unifyLNTerm [Equal t1 t2] `runReader` hnd

-- *****************************************************************************
-- Tests aggregate for homomorphic encryption
-- *****************************************************************************

testAllHomomorphic :: MaudeHandle -> Test
testAllHomomorphic mhnd = TestLabel "All Homomorphic Tests" $
  TestList
    [ testsMatchingHomomorphic mhnd
    , testsUnifyHomomorphic mhnd
    , testsUnifyHomomorphicSf mhnd
    , testsUnifyHomomorphicRules mhnd
    , testPrinterHomomorphic mhnd
    ]

-- *****************************************************************************
-- Tests for Matching modulo EpsilonH (For Homomorphic encryption)
-- *****************************************************************************

-- match t p tries to find a substitution phi such that "t == phi applied to p"
testsMatchingHomomorphic :: MaudeHandle -> Test
testsMatchingHomomorphic mhnd = TestLabel "Tests for Matching modulo EpsilonH" $
  TestList $ map (\(testName, testOutcome, term1, term2) -> testMatchingHomWithPrint mhnd testName testOutcome term1 term2)
    -- small examples
    [ ("a",                 True,   x0,           x0           )
    , ("b",                 True,   x1,           x0           )
    , ("c",                 True,   pair(x1,x2),  x0           )
    , ("d",                 False,  pair(x0,x2),  x0           )
    , ("e",                 False,  x0,           pair(x0,x2)  )
    , ("f",                 False,  pair(x0,x1),  pair(x1,x2)  )
    -- bigger examples
    , ("homdef 1",          True,   henc (pair (x0,x1), x2),              pair (henc (x0,x2), henc (x1,x2))   )
    , ("homdef 2",          True,   pair (henc (x0,x2), henc (x1,x2)),    henc (pair (x0,x1), x2)             )
    , ("homdef1diffVars 1", True,   henc (pair (x0,x0), x0),              pair (henc (x0,x2), henc (x1,x2))   )
    , ("homdef1diffVars 2", False,  pair (henc (x0,x2), henc (x1,x2)),    henc (pair (x0,x0), x0)             )
    , ("pair 1",            True,   pair (pair (x0,x0), x0),              pair (pair (x2,x3), x4)             )
    , ("pair 2",            False,  pair (pair (x2,x3), x4),              pair (pair (x0,x0), x0)             )
    -- cases with different sorts
    , ("public 1",          False,  x0,     px0     )
    , ("public 2",          True,   px0,    x0      )
    , ("fresh 1",           False,  x0,     fx0     )
    , ("fresh 2",           True,   fx0,    x0      )
    , ("nat 1",             False,  x0,     nn1     )
    , ("nat 2",             True,   nn1,    x0      )
    , ("publicnat 1",       False,  px0,    nn1     )
    , ("publicnat 2",       False,  nn1,    px0     )
    , ("publicfresh 1",     False,  px0,    fx0     )
    , ("publicfresh 2",     False,  fx0,    px0     )
    , ("freshnat 1",        False,  fx0,    nn1     )
    , ("freshnat 2",        False,  nn1,    fx0     )
    , ("same fresh",        True,   fx0,    fx0     )
    , ("same nat",          True,   nn1,    nn1     )
    , ("same pub",          True,   px0,    px0     )
    , ("same fresh 2",      True,   fx0,    fx1     )
    , ("same nat 2",        True,   nn1,    nn2     )
    , ("same pub 2",        True,   px0,    px1     )
    , ("node 1",            True,   node1,  node1   )
    , ("node 2",            True,   node1,  node2   )
    , ("node 3",            False,  node1,  x0      )
    ]

testMatchingHomWithPrint :: MaudeHandle -> String -> Bool -> LNTerm -> LNTerm -> Test
testMatchingHomWithPrint mhnd caseName caseOutcome t1 t2 =
  TestLabel caseName $ TestCase $ assertBool (
    "------ TEST PRINTER ------" ++ "\n"
    ++ "Case:        " ++ caseName ++ "\n"
    ++ "Terms:       " ++ show t1 ++ ", " ++ show t2 ++ "\n"
    ++ "--- matchLNTerm ---" ++ "\n"
    ++ "NumMatchers: " ++ show numMatchers ++ "\n"
    ++ "Fst Matcher: " ++ show subst ++ "\n"
    ++ "New Terms:   " ++ show t1 ++ ", " ++ show t2Subst ++ "\n"
    ++ "--- matchHomLNTerm ---" ++ "\n"
    ++ "Did-Match    " ++ show substHMatches ++ "\n"
    ++ "Matcher:     " ++ show substH' ++ "\n"
    ++ "New Terms:   " ++ show t1 ++ ", " ++ show t2SubstH ++ "\n"
    ++ "--- with normed terms ---" ++ "\n"
    ++ "Terms:       " ++ show t1N ++ ", " ++ show t2N ++ "\n"
    ++ "New Terms:   " ++ show t1N ++ ", " ++ show t2NSubstH ++ "\n"
    ++ "------ END TEST PRINTER ------"
    ++ "Note: x.2 <~ x means x is being replaced by x.2" ++ "\n"
  ) (
    caseOutcome == substHMatches &&   -- equal to expected outcome
    caseOutcome == (t1N == t2NSubstH) -- terms equal after norming
  )
  where
    t1N = normHomomorphic t1
    t2N = normHomomorphic t2

    substs = solveMatchLNTerm (t1 `matchWith` t2) `runReader` mhnd
    numMatchers = length substs
    subst = safeHead substs

    substH = matchHomomorphicLTerm sortOfName [(t1N, t2N)]
    substH' = fromMaybe emptySubst substH

    t2Subst = applyVTerm subst t2
    t2SubstH = applyVTerm substH' t2
    t2NSubstH = normHomomorphic $ applyVTerm substH' t2N

    substHMatches = case substH of
      Just _ -> True
      _      -> False

    safeHead s = if null s then Subst $ M.fromList [(LVar "NOSUBST" LSortMsg 0,x0)] else head s

-- *****************************************************************************
-- Tests for Unification modulo EpsilonH (For Homomorphic encryption)
-- *****************************************************************************

-- Multiple tests for unification modulo EpisolonH algorithm 
-- implemented in unifyHomomorphicLNTerm
testsUnifyHomomorphic :: MaudeHandle -> Test
testsUnifyHomomorphic mhnd = TestLabel "Tests for Unify modulo EpsilonH" $
  TestList $ map (\(testName, testOutcome, term1, term2) -> testUnifyWithPrint mhnd testName testOutcome term1 term2)
    [ ("1",         True,   x0,                                                             x0                                                                            )
    , ("2",         True,   x0,                                                             x1                                                                            )
    , ("3",         False,  henc(x0,x1),                                                    x1                                                                            )
    , ("4",         True,   x0,                                                             henc(x1,x2)                                                                   )
    , ("5",         True,   henc( pair (x0,x1), x2),                                        x4                                                                            )
    , ("6",         True,   henc( henc (pair (x0,x1), x2),x0),                              henc(x5,x6)                                                                   )
    , ("7",         True,   pair(x0,x0),                                                    pair(x1,x2)                                                                   )
    , ("8",         True,   pair(x0,x1),                                                    henc(x2,x3)                                                                   )
    , ("9",         True,   henc(x0,x1),                                                    pair(x2,x3)                                                                   )
    , ("10",        True,   pair(x0,x0),                                                    henc(x2,x3)                                                                   )
    , ("11",        True,   henc(x0,x1),                                                    pair(x2,x2)                                                                   )
    , ("12",        False,  pair(x0,x1),                                                    henc(x1,x3)                                                                   )
    , ("13",        False,  henc(x2,x1),                                                    pair(x2,x3)                                                                   )
    , ("14",        True,   pair(x0,x1),                                                    henc(x2,x2)                                                                   )
    , ("15",        True,   henc(x0,x0),                                                    pair(x2,x3)                                                                   )
    , ("16",        False,  pair(x0,x1),                                                    henc(x2,x0)                                                                   )
    , ("17",        False,  henc(x0,x2),                                                    pair(x2,x3)                                                                   )    
    , ("defhenc 1", True,   henc( pair (x0,x1), x2),                                        pair (henc (x0,x2), henc (x1,x2))                                             )
    , ("defhenc 2", True,   pair( henc (x0,x2), henc (x1,x2)),                              henc (pair (x0,x1), x2)                                                       )
    , ("defhenc 3", True,   henc( henc (pair (x0,x1), x2),x0),                              henc(henc (pair (x0,x1), x2),x0)                                              )
    , ("symEnc 1",  False,  senc( pair (x0,x1), x2),                                        pair (senc (x0,x2), senc (x1,x2))                                             )
    , ("norm 1",    True,   pair( pair (x0,x0), x0),                                        pair (pair (x2,x3), x4)                                                       )
    , ("norm 2",    True,   pair( pair (x2,x3), x4),                                        pair (pair (x0,x0), x0)                                                       )
    , ("norm 3",    True,   henc( pair (x0,x0), x0),                                        pair (henc (x1,x2), henc (x3,x4))                                             )
    , ("norm 4",    True,   henc( pair (x0,x0), x0),                                        pair (henc (x1,x2), henc (x2,x4))                                             )
    , ("norm 5",    True,   henc( pair (x0,x1), x2),                                        henc(x3,x4)                                                                   )
    , ("norm 6",    True,   henc( henc (pair(x0,x1),x2),x3),pair(henc(henc(x0,x2),x3),      henc(henc(x1,x2),x3))                                                         )
    , ("norm 7",    True,   henc( pair (henc(pair(x0,x1),x2), pair(henc(x3,x4),x5)), x6),   normHomomorphic (henc( pair(henc(pair(x0,x1),x2), pair(henc(x3,x4),x5)), x6)) )
    -- cases with different sorts
    , ("public 1",  True,   x0,           px0           )
    , ("public 2",  True,   px0,          x0            )
    , ("fresh 1",   True,   x0,           fx0           )
    , ("fresh 2",   True,   fx0,          x0            )
    , ("nat 1",     True,   x0,           nn1           )
    , ("nat 2",     True,   nn1,          x0            )
    , ("pubnat 1",  False,  px0,          nn1           )
    , ("pubnat 2",  False,  nn1,          px0           )
    , ("pubfr 1",   False,  px0,          fx0           )
    , ("pubfr 2",   False,  fx0,          px0           )
    , ("frnat 1",   False,  fx0,          nn1           )
    , ("frnat 2",   False,  nn1,          fx0           )
    , ("multi 1",   True,   pair(x0,x1),  pair(px0,px1) )
    , ("multi 2",   True,   pair(x0,px0), pair(px0,x0)  )
    , ("multi 3",   True,   pair(x0,nn1), pair(px0,x1)  )
    , ("samefr",    True,   fx0,          fx0           )
    , ("samenat",   True,   nn1,          nn1           )
    , ("samepub",   True,   px0,          px0           )
    , ("samefr 2",  True,   fx0,          fx1           )
    , ("samenat 2", True,   nn1,          nn2           )
    , ("samepub 2", True,   px0,          px1           )
     -- timepoint cases
    , ("node 1",    True,   node1,        node1         )
    , ("node 2",    True,   node1,        node2         )
    , ("node 3",    False,  node1,        x0            )
    ]

testUnifyWithPrint :: MaudeHandle -> String -> Bool -> LNTerm -> LNTerm -> Test
testUnifyWithPrint mhnd caseName caseOutcome t1 t2 =
  TestLabel caseName $ TestCase $ assertBool (
    "------ TEST PRINTER ------" ++ "\n"
    ++ "Case:          " ++ caseName ++ "\n"
    ++ "Terms:         " ++ show t1 ++ ", " ++ show t2 ++ "\n"
    ++ "--- unifyLNTerm ---" ++ "\n"
    ++ "NumUnifiers:   " ++ show numUnifiers ++ "\n"
    ++ "First unifier: " ++ show subst ++ "\n"
    ++ "After fTFA:    VSubst: " ++ show subst' ++ "\n"
    ++ "New Terms:     " ++ show t1Subst' ++ ", " ++ show t2Subst' ++ "\n"
    ++ "--- unifyHomomorphicLTerm ---" ++ "\n" 
    ++ "First unifier: " ++ show substH ++ "\n"
    ++ "New Terms:     " ++ show t1SubstH ++ ", " ++ show t2SubstH ++ "\n"
    ++ "After fTFA:    VSubst: " ++ show substH' ++ "\n"
    ++ "New Terms:     " ++ show t1SubstH' ++ ", " ++ show t2SubstH' ++ "\n"
    ++ "--- with normed terms ---" ++ "\n"
    ++ "First unifier: " ++ show substH ++ "\n"
    ++ "New Terms:     " ++ show t1NSubstH ++ ", " ++ show t2NSubstH ++ "\n"
    ++ "After fTFA:    VSubst: " ++ show substH' ++ "\n"
    ++ "New Terms:     " ++ show t1NSubstH' ++ ", " ++ show t2NSubstH' ++ "\n"
    ++ "Note:          x.2 <~ x means x is being replaced by x.2" ++ "\n"
    ++ "------ END TEST PRINTER ------"
  ) (
    caseOutcome == substHUnifies &&            -- unification found
    caseOutcome == (t1NSubstH == t2NSubstH) && -- normed terms equal after unification
    caseOutcome == (t1NSubstH' == t2NSubstH')  -- freshToAvoid does not change the outcome
  )
  where
    substs = unifyLTerm sortOfName [Equal t1 t2] `runReader` mhnd
    numUnifiers = length substs
    subst = safeHead substs
    subst' = freshToFreeAvoiding subst [t1,t2]

    substHUnifier = unifyHomomorphicLTerm sortOfName [Equal t1 t2]
    substH = case substHUnifier of
      Just (s,_) -> s
      Nothing    -> emptySubst
    substH' = case substHUnifier of
      Just (_,s) -> freshToFreeAvoiding s [t1,t2]
      Nothing    -> emptySubst
    substHUnifies = case substHUnifier of
      Just (_,_) -> True
      Nothing    -> False

    t1Subst' = applyVTerm subst' t1
    t2Subst' = applyVTerm subst' t2

    t1SubstH = applyVTerm substH t1
    t2SubstH = applyVTerm substH t2
    t1SubstH' = applyVTerm substH' t1
    t2SubstH' = applyVTerm substH' t2

    t1NSubstH = normHomomorphic $ applyVTerm substH t1
    t2NSubstH = normHomomorphic $ applyVTerm substH t2
    t1NSubstH' = normHomomorphic $ applyVTerm substH' t1
    t2NSubstH' = normHomomorphic $ applyVTerm substH' t2

    safeHead s = if null s then SubstVFresh $ M.fromList [(LVar "NOSUBST" LSortMsg 0,x0)] else head s

-- *****************************************************************************
-- Tests for Subfunctions of the Unification Algorithm modulo EpsilonH
-- *****************************************************************************

-- Multiple tests for the functions directly used by the 
-- homomorphic encrytion unification algorithm 
testsUnifyHomomorphicSf :: MaudeHandle -> Test
testsUnifyHomomorphicSf _ =
  TestLabel "Tests for Unify module EpsilonH subfunctions" $
  TestList
    [ testTrue "position var" (positionsWithTerms x0 == [("",x0)])
    , testTrue "position func1" (positionsWithTerms t1 == posT1)
    , testTrue "position func2" (positionsWithTerms t2 == posT2)
    , testTrue "ppos paper" (pPosition "112" tpaper1 == "12")
    , testTrue "epos paper" (ePosition "112" tpaper1 == "1")
    , testTrue "purePPos paper" (findPurePPositions tpaper2 == pPurePosTPaper2)
    , testTrue "maxPPurePos paper" (maximalPositions (findPurePPositions tpaper2) == maxPPurePosTPaper2)
    , testTrue "penukEPos" (findPenukEPositions tpaper3 == ePenukPosTPaper3)
    , testTrue "maxPenukEPos" (maximalPositions (findPenukEPositions tpaper3) == maxEPenukPosTPaper3)
    , testTrue "fromtoERep 1" (fromERepresentation (buildERepresentation t1) == t1)
    , testTrue "fromtoERep 2" (fromERepresentation (buildERepresentation t2) == t2)
    , testTrue "fromtoERep paper1" (fromERepresentation (buildERepresentation tpaper1) == tpaper1)
    , testTrue "fromtoERep paper2" (fromERepresentation (buildERepresentation tpaper2) == tpaper2)
    , testTrue "fromtoERep paper3" (fromERepresentation (buildERepresentation tpaper3) == tpaper3)
    , testTrue "fromtoPRep 1" (fromPRepresentation (buildPRepresentation t1) == t1)
    , testTrue "fromtoPRep 2" (fromPRepresentation (buildPRepresentation t2) == t2)
    , testTrue "fromtoPRep paper1" (fromPRepresentation (buildPRepresentation tpaper1) == tpaper1)
    , testTrue "fromtoPRep paper2" (fromPRepresentation (buildPRepresentation tpaper2) == tpaper2)
    , testTrue "fromtoPRep paper3" (fromPRepresentation (buildPRepresentation tpaper3) == tpaper3)
    , testTrue "fromtoERep pair" (fromERepresentation (buildERepresentation tP1) == tP1)
    , testTrue "fromtoERep henc" (fromERepresentation (buildERepresentation tH1) == tH1)
    , testTrue "fromtoPRep pair" (fromPRepresentation (buildPRepresentation tP1) == tP1)
    , testTrue "fromtoPRep henc" (fromPRepresentation (buildPRepresentation tH1) == tH1)
    , testTrue "norm1" (normHomomorphic x0 == x0)
    , testTrue "norm2" (normHomomorphic (pair(x0,x1)) == pair(x0,x1))
    , testTrue "norm3" (normHomomorphic (henc(pair(x0,x1),x2)) == pair(henc(x0,x2),henc(x1,x2)))
    , testTrue "sanityCheck" (not (allLeftVarsNotRight [
        (LVar "x0" LSortMsg 15, pair(varTerm $ LVar "x"  LSortMsg 22, varTerm $ LVar "x"  LSortMsg 23)), 
        (LVar "x2" LSortMsg 17, varTerm $ LVar "x2" LSortMsg 21), 
        (LVar "x"  LSortMsg 19, henc(varTerm $ LVar "x"  LSortMsg 22, varTerm $ LVar "x2" LSortMsg 21)), 
        (LVar "x"  LSortMsg 20, henc(varTerm $ LVar "x"  LSortMsg 23, varTerm $ LVar "x2" LSortMsg 21)), 
        (LVar "x"  LSortMsg 21, varTerm $ LVar "x"  LSortMsg 22),    -- x2 21 is on the right side
        (LVar "x"  LSortMsg 22, varTerm $ LVar "x"  LSortMsg 23) ])) -- x 22 is on the right side multiple times
    -- example:
    -- henc( henc( pair(x0,x1), k0), k1) 
    -- -> henc( pair( henc(x0,k0), henc(x1,k0) ), k1)
    -- -> pair( henc(henc(x0,k0),k1) , henc(henc(x1,k0),k1) )
    , testTrue "norm4" (normHomomorphic norm1 == norm2)
    , testTrue "norm5" (normHomomorphic tpaper1 == tpaper1N)
    , testTrue "norm6" (normHomomorphic tpaper2 == tpaper2N)
    , testTrue "norm7" (normHomomorphic tpaper3 == tpaper3)
    ]
  where
    t1 = henc (pair (x0,x1),x2)
    posT1 =
      [ ("", henc (pair (x0,x1),x2) )
      , ("1", pair (x0,x1) )
      , ("11", x0 )
      , ("12", x1 )
      , ("2", x2 ) ]
    t2 = pair (henc (x0,x2),henc (x1,x2))
    posT2 =
      [ ("", pair (henc (x0,x2),henc (x1,x2)) )
      , ("1", henc (x0,x2) )
      , ("11", x0 )
      , ("12", x2 )
      , ("2", henc (x1,x2) )
      , ("21", x1 )
      , ("22", x2 ) ]
    tpaper1 = pair( henc( pair(x0,x2), x4), x3 )
    tpaper1N = pair( pair(henc(x0,x4),henc(x2,x4)), x3 )
    tpaper2 = pair( pair(x0,x1), henc(pair (x2,x3), x4))
    tpaper2N = pair( pair(x0,x1), pair(henc(x2,x4),henc(x3,x4)) )
    pPurePosTPaper2 =
      [ ("", tpaper2 )
      , ("1", pair (x0,x1) )
      , ("11", x0 )
      , ("12", x1 )
      , ("2", henc (pair (x2,x3),x4) ) ]
    maxPPurePosTPaper2 =
      [ ("11", x0 )
      , ("12", x1 )
      , ("2", henc (pair (x2,x3),x4) ) ]
    tpaper3 = henc (henc (x0,x1),henc (x2,x3))
    ePurePosTPaper3 =
      [ ("", tpaper3 )
      , ("1", henc (x0,x1) )
      , ("11", x0 )
      , ("12", x1 )
      , ("2", henc (x2,x3) )
      , ("21", x2 )
      , ("22", x3 ) ]
    ePenukPosTPaper3 =
      [ ("", tpaper3 )
      , ("1", henc (x0,x1) )
      , ("11", x0 )
      , ("12", x1 )
      , ("2", henc (x2,x3) ) ]
    maxEPenukPosTPaper3 =
      [ ("11", x0 )
      , ("12", x1 )
      , ("2", henc (x2,x3) ) ]
    norm1 = henc(henc(pair(x0,x1),x2),x3)
    norm2 = pair(henc(henc(x0,x2),x3), henc(henc(x1,x2),x3))
    tH1 = henc(x0, x1)
    tP1 = pair(x0, x1)

-- *****************************************************************************
-- Tests for specific rules of the Homomorphic Unification Algorithm
-- *****************************************************************************

-- debugHomomorphicRule: 
--  [ failureOneHomomorphicRule             0
--  , failureTwoHomomorphicRule             1
--  , occurCheckHomomorphicRule             2
--  , clashHomomorphicRule                  3
--  , differentConsts                       4
--  , doSortsCompare                        5
--  , shapingHomomorphicRule                6
--  , parsingHomomorphicRule                7
--  , variableSubstitutionHomomorphicRule   8
--  , trivialHomomorphicRule                9
--  , stdDecompositionHomomorphicRule]      10
testsUnifyHomomorphicRules :: MaudeHandle -> Test
testsUnifyHomomorphicRules _ = TestLabel "Tests for Unify module EpsilonH Rules" $
  TestList
    [ testTrue "trivial 1" (debugHomomorphicRule 9 tE1 s ([], vA [tE1]) == HEqs ([],[]) )
    , testTrue "trivial 2" (debugHomomorphicRule 9 tFE1 s ([], vA [tFE1]) == HEqs ([],[]) )
    , testTrue "trivial 3" (debugHomomorphicRule 9 tE2 s ([], vA [tE2]) == HNothing)
    , testTrue "std dec 1" (debugHomomorphicRule 10 tFE2 s ([], vA [tFE2]) == HEqs ([tE2, tE3],[]) )
    , testTrue "std dec 2" (debugHomomorphicRule 10 tFE3 s ([], vA [tFE3]) == HNothing)
    , testTrue "var sub 1" (debugHomomorphicRule 8 tHE1 s ([], vA [tHE1]) == HNothing)
    , testTrue "var sub 2" (debugHomomorphicRule 8 tHE1 s ([tE3], vA [tHE1, tE3]) == HNothing)
    , testTrue "var sub 3" (debugHomomorphicRule 8 tHE1 s ([tE2], vA [tHE1, tE2]) == HSubstEqs tHE1S ([tHE1],[]) )
    , testTrue "var sub 4" (debugHomomorphicRule 8 tHE1 s ([tFE2], vA [tHE1, tFE2]) == HSubstEqs tHE1S ([tHE1],[]) )
    , testTrue "var sub 5" (debugHomomorphicRule 8 tE2 s ([tFE2], vA [tE2, tFE2]) == HSubstEqs tE2S ([tE2],[]) )
    , testTrue "var sub 6" (debugHomomorphicRule 8 tHE2 s ([], vA [tHE2]) == HNothing)
    , testTrue "var sub 7" (debugHomomorphicRule 8 tHE2 s ([tE3], vA [tHE2, tE3]) == HNothing)
    , testTrue "var sub 8" (debugHomomorphicRule 8 tHE2 s ([tE2], vA [tHE2, tE2]) == HNothing)
    , testTrue "clash   1" (debugHomomorphicRule 3 tFE1 s ([], vA [tFE1]) == HNothing)
    , testTrue "clash   2" (debugHomomorphicRule 3 tFE3 s ([], vA [tFE3]) == HNothing)
    , testTrue "clash   3" (debugHomomorphicRule 3 tFE4 s ([], vA [tFE4]) == HFail)
    , testTrue "occur   1" (debugHomomorphicRule 2 tFE4 s ([], vA [tFE4]) == HNothing)
    , testTrue "occur   2" (debugHomomorphicRule 2 tE1 s ([], vA [tE1]) == HNothing)
    , testTrue "occur   3" (debugHomomorphicRule 2 tE2 s ([], vA [tE2]) == HNothing)
    , testTrue "occur   4" (debugHomomorphicRule 2 tHE1 s ([], vA [tHE1]) == HNothing)
    , testTrue "occur   5" (debugHomomorphicRule 2 tHE2 s ([], vA [tHE2]) == HFail)
    , testTrue "shaping 1" (debugHomomorphicRule 6 tFFE1 s ([], vA [tFFE1]) == HNothing) -- resolved by standard decomposition rule
    , testTrue "shaping 2" (debugHomomorphicRule 6 tFFE1 s ([tFFE2], vA [tFFE1, tFFE2]) == HNothing)
    , testTrue "shaping 3" (debugHomomorphicRule 6 tFE2 s ([], vA [tFE2]) == HNothing)
    , testTrue "shaping 4" (debugHomomorphicRule 6 tHE2 s ([], vA [tHE2]) == HNothing)
    , testTrue "shaping 5" (debugHomomorphicRule 6 tFFE4 s ([tFFE2], vA [tFFE4, tFFE2]) == HNothing)
    , testTrue "fail1   1" (debugHomomorphicRule 0 tFE5 s ([], vA [tFE5]) == HFail)
    , testTrue "fail1   2" (debugHomomorphicRule 0 tFE1 s ([], vA [tFE1]) == HNothing)
    , testTrue "fail1   3" (debugHomomorphicRule 0 tFFE1 s ([], vA [tFFE1]) == HNothing)
    , testTrue "fail1   4" (debugHomomorphicRule 0 tFE6 s ([], vA [tFE6]) == HNothing)
    , testTrue "fail2   1" (debugHomomorphicRule 1 tFFE5 s ([], vA [tFFE5]) == HFail)
    , testTrue "fail2   2" (debugHomomorphicRule 1 tFFE1 s ([], vA [tFFE1]) == HNothing)
    , testTrue "fail2   3" (debugHomomorphicRule 1 tE1 s ([], vA [tE1]) == HNothing)
    , testTrue "fail2   4" (debugHomomorphicRule 1 tFFE6 s ([], vA [tFFE6]) == HNothing)
    , testTrue "fail2   5" (debugHomomorphicRule 1 tFFE7 s ([], vA [tFFE7]) == HNothing)
    , testTrue "parsing 1" (debugHomomorphicRule 7 tFE1 s ([], vA [tFE1]) == HEqs ([tE1, tE4],[]) )
    , testsUnifyHomomorphicShaping
    ]
  where
    tE1 = Equal (fH x0) (fH x0)
    tE2 = Equal (fH x0) (fH x2)
    tE3 = Equal (fH x1) (fH x3)
    tE4 = Equal (fH x1) (fH x1) 
    tFE1 = Equal (fH (henc (x0,x1))) (fH (henc (x0,x1)))
    tFE2 = Equal (fH (henc (x0,x1))) (fH (henc (x2,x3)))
    tFE3 = Equal (fH (pair (x0,x1))) (fH (henc (x2,x3)))
    tFE4 = Equal (fH (sdec (x0,x1))) (fH (henc (x2,x3)))
    tFE5 = Equal (fH (pair (x0,x1))) (fH (henc (x0,x3))) -- out of phase on t5
    tFE6 = Equal (fH (henc (x0,x1))) (fH (henc (x0,x2)))
    tHE1 = Equal (fH x0) (fH (henc (x2,x3)))
    tHE1S = [(LVar "x" LSortMsg 0, henc (x2,x3))]
    tE2S = [(LVar "x" LSortMsg 0, x2)]
    tHE2 = Equal (fH x0) (fH (henc (x2,x0)))
    tFFE1 = Equal (fH (henc (x0,x1))) (fH (henc (henc (x2,x3),x4)))
    tFFE2 = Equal (fH (henc (henc (x5,x3),x1))) (fH (henc (henc (x2,x3),x4)))
    tFFE2' = Equal (fH (henc (henc (x6,x3),x1))) (fH (henc (henc (x2,x3),x4)))
    tFFE3 = Equal (fH x0) (fH (henc (x5,x3)))
    tFFE3' = Equal (fH x0) (fH (henc (x6,x3)))
    tFFE4 = Equal (fH x0) (fH (henc (henc (x2,x3),x4)))
    tFFE5 = Equal (fH (pair (henc (pair (x0,x1),x2),x3))) (fH (henc (henc (x4,x5),x6)))
    tFFE6 = Equal (fH (pair (henc (x0,x2),x3))) (fH (henc (henc (x4,x5),x6)))
    tFFE7 = Equal (fH (pair (henc (pair (x0,x1),x2),x3))) (fH (henc (x4,x6)))
    s = sortOfName
    fH = toLPETerm
    vA = sortednub . concatMap (varsVTerm . lTerm) . concatMap (\(Equal l r) -> [l,r])
    -- shaping:  tFFE1 = Equal P [""] [[x,x.1]] E [x.2,x.3,x.4] with n = 2, m = 2
    --    Return tFFE2 = Equal P [""] [[xH.1, x.3, x.1]] E [x.2,x.3,x.4]
    --           tFFE3 = Equal x.0                       E [xH.1, x.3]
    -- failure2: tFFE5 = Equal P ["1","2"] [[pair(x,x.1),x.2],[x.3]] 
    --                         E [x.4,x.5,x.6] with n = 2, m = 1

testsUnifyHomomorphicShaping :: Test
testsUnifyHomomorphicShaping = TestLabel "Tests for Unify module EpsilonH Shaping Rule" $
  TestList 
   [ testTrue "Shaping 1" (debugHomomorphicRule 6 pairHenc1 s ([], vA [pairHenc1]) == HEqs ([pairHenc1Shaped1, pairHenc1Shaped2], [sh1V]))
   , testTrue "Shaping 2" (debugHomomorphicRule 6 pairHenc2 s ([], vA [pairHenc2]) == HEqs ([pairHenc2Shaped1, pairHenc2Shaped2], [sh1V]))
   ]
  where
    -- example 1:
    pairHenc1        = Equal (fH (pair(x0,x1)))                     (fH (henc(x2,x3))) -- n = 1, m = 1 or 2 with {km,...,kn} = {}
    --                 P(E(x0),E(x1))                               E(x2,x3)
    --                 x = x0, km,..,kn = {}                        s = x2, k1' = kn' = x3
    --                 x' = sh1, k1',..,km-1' = x3
    --              -> P(..,E(sh1,x3),..)                           E(x2,x3)  
    pairHenc1Shaped1 = Equal (fH (pair(henc(sh1,x3),x1)))           (fH (henc(x2,x3)))
    --              -> x0                                           E(sh1,x3)
    pairHenc1Shaped2 = Equal (fH x0)                                (fH (henc(sh1,x3)))
    -- example 2:
    pairHenc2        = Equal (fH (pair(x0,x1)))                     (fH (henc(henc(x2,x3),x4))) -- n = 2, m = 2 or 3 with {km,...,kn} = {}
    --                 P(E(x0),E(x1))                               E(x2,x3,x4)
    --                 x = x0, km,..,kn = {}                        s = x2, k1',..,kn' = x3,x4
    --                 x' = sh1, k1',..,km-1' = x3,x4
    --              -> P(..,E(sh1,x3,x4))                           E(x2,x3,x4)
    pairHenc2Shaped1 = Equal (fH (pair(henc(henc(sh1,x3),x4),x1)))  (fH (henc(henc(x2,x3),x4)))
    pairHenc2Shaped2 = Equal (fH x0)                                (fH (henc(henc(sh1,x3),x4)))
    -- vars
    sh1V = LVar "sh" LSortMsg 1 
    sh1 = varTerm sh1V
    sh2V = LVar "sh" LSortMsg 2
    sh2 = varTerm sh2V
    -- helper:
    s = sortOfName
    fH = toLPETerm
    vA = sortednub . concatMap (varsVTerm . lTerm) . concatMap (\(Equal l r) -> [l,r])
    

-- *****************************************************************************
-- Specific printer
-- *****************************************************************************

-- Test used to print return values and variables for debugging
-- Set Test return value to false to print out text
testPrinterHomomorphic :: MaudeHandle -> Test
testPrinterHomomorphic _ =
  TestLabel "prints out debugging information" $
  TestList
    [ testTrue (show "***text being printed***") True]
  where
    s = sortOfName

-- *****************************************************************************
-- Tests for Substitutions
-- *****************************************************************************

testsSubst :: Test
testsSubst = TestLabel "Tests for Substitution" $
    TestList
      [ -- introduce renaming for x3
        testEqual "a" (substFromListVFresh [(lx1, p1), (lx2, x6), (lx3,x6), (lx5, p1)])
                      (composeVFresh (substFromListVFresh [(lx5, p1)])
                                     (substFromList [(lx1, x5), (lx2, x3)]))
        -- rename (fresh) x6 in s1b and do not mix up with x6 in s3f
      , testEqual "b" s1b_o_s3f (composeVFresh s1b s3f)
        -- drop x1 |-> p1 mapping from s1b, but apply to x2 |-> pair(x3,x1) in s3f
      , testEqual "c" s1b_o_s4f (composeVFresh s1b s4f)
      , testEqual "d" s4f_o_s3f (compose s4f s3f)
      , testEqual "e" (substFromList [(lx1,f1), (lx2,f1)])
                      (mapRange (const f1) s4f)
      , testTrue  "f" (isRenaming (substFromListVFresh [(lx1,x3), (lx2,x2), (lx3,x1)]))

      , testEqual "g" (substFromListVFresh [(lx1, f1)])
                      (extendWithRenaming [lx1] (substFromListVFresh [(lx1, f1)]))

      , testEqual "h" (substFromListVFresh [(lx2, x1), (lx1, x2)])
                      (extendWithRenaming [lx1] (substFromListVFresh [(lx2, x1)]))
      -- trivial, increase coverage
      , testTrue "i" ((>0) . length $ show s1b)
      , testTrue "j" ((>0) . length $ (render $ prettyLSubstVFresh s1b))
      , testTrue "k" (not . null $ domVFresh s1b)
      , testTrue "l" (not . null $ varsRangeVFresh s1b)
      , testTrue "m" ((>0) . length $ show $ substToListOn [lx1] s4f)
      , testTrue "n" ((<100) . size $ emptySubst)
      , testTrue "o" ((<10000) . size $ s1b)
      , testTrue "p" ((<100) . size $ emptySubstVFresh)
      ]
  where
    s1b       = substFromListVFresh [(lx1, p1), (lx2, x6), (lx3, x6), (lx4, f1)]
    s3f       = substFromList [(lx8, x6), (lx2, pair (x2,x1))]
    s1b_o_s3f = substFromListVFresh -- x2 not identified with x8
                  [(lx1, p1), (lx2, pair (x9, p1)), (lx3, x9), (lx4, f1), (lx6, x10), (lx8, x10)]
    s4f       = substFromList [(lx1, x6), (lx2, pair (x3,x1))]
    s1b_o_s4f = substFromListVFresh
                  [(lx1, x8), (lx2, pair (x7, p1)), (lx3, x7), (lx4, f1), (lx6, x8)]

    s4f_o_s3f = substFromList [(lx1, x6), (lx2, pair (pair (x3,x1),x6)), (lx8, x6)]
    x15 = varTerm $ LVar "x" LSortMsg 15
    x13 = varTerm $ LVar "x" LSortMsg 13
    x20 = varTerm $ LVar "x" LSortMsg 20
    x22 = varTerm $ LVar "x" LSortMsg 22

-- *****************************************************************************
-- Tests for Subsumption
-- *****************************************************************************

testsSubs :: MaudeHandle -> Test
testsSubs mhnd = TestLabel "Tests for Subsumption" $ TestList
    [ tct Nothing f1 f2
    , tct (Just EQ) x1   x2
    , tct (Just LT) x1   (x1 *: x1)
    , tct (Just GT) (x1 *: x1) x1
    , tct (Just GT) (pair (f1 *: f2,f1)) (pair (f2 *: f1,x2))
    , testEqual "a" [substFromList [(lx2, pair (x6,x7)), (lx3, p1)]]
                    (factorSubstVia [lx1]
                                    (substFromList [(lx1,pair (pair (x6,x7),p1))])
                                    (substFromList [(lx1,pair (x2,x3))]) `runReader` mhnd)

    , testEqual "b" [substFromList [(lx2, pair (x6,x7)), (lx3, p1), (lx5, f1), (lx6,f2)]]
                    (factorSubstVia [lx1, lx5, lx6]
                       (substFromList [(lx1,pair (pair (x6,x7),p1)), (lx5,f1), (lx6,f2)])
                       (substFromList [(lx1,pair (x2,x3))]) `runReader` mhnd)

    , testTrue "c" (eqTermSubs p1 p1 `runReader` mhnd)
    ]
  where
     tct res e1 e2 =
         testEqual ("termCompareSubs "++ppLTerm e1++" "++ppLTerm e2) res (compareTermSubs e1 e2 `runReader` mhnd)

ppLTerm :: LNTerm -> String
ppLTerm = render . prettyNTerm

ppLSubst :: LNSubst -> String
ppLSubst = render . prettyLNSubst

-- *****************************************************************************
-- Tests for Norm
-- *****************************************************************************

testsNorm :: MaudeHandle -> Test
testsNorm hnd = TestLabel "Tests for normalization" $ TestList
    [ tcn normBigTerm  bigTerm
    , tcn (expo (f3,f1  *:  f4))
          (expo (expo (f3,f4),f1 *: f1 *: f2 *: inv (inv (inv f1)) *: one *: expo (inv f2,one)))
    , tcn (mult [f1, f1, f2]) (f1  *:  (f1  *:  f2))
    , tcn (inv (f1  *:  f2)) (inv f2  *:  inv f1)
    , tcn (f1  *:  inv f2) (f1  *:  inv f2)
    , tcn (one::LNTerm) one
    , tcn x6 (expo (expo (x6,inv x3),x3))

--    , testEqual "a" (normAC (p3 *: (p1 *: p2))) (mult [p1, p2, p3])
--    , testEqual "b" (normAC (p3 *: (p1 *: inv p3))) (mult [p1, p3, inv p3])
--    , testEqual "c" (normAC ((p1 *: p2) *: p3)) (mult [p1, p2, p3])
--    , testEqual "d" (normAC t1) (mult [p1, p2, p3, p4])
--    , testEqual "e" (normAC ((p1 # p2) *: p3)) (p3 *: (p1 # p2))
--    , testEqual "f" (normAC (p3 *: (p1 # p2))) (p3 *: (p1 # p2))
--    , testEqual "g" (normAC ((p3 *: p4) *: (p1 # p2))) (mult [p3, p4, p1 # p2])
    ]
  where
    tcn e1 e2 = testEqual ("norm "++ppLTerm e2) e1 (norm' e2 `runReader` hnd)
    t1 = (p1 *: p2) *: (p3 *: p4)

-- *****************************************************************************
-- Tests for Term
-- *****************************************************************************

testsTerm :: Test
testsTerm = TestLabel "Tests for Terms" $ TestList
    [ uncurry (testEqual "Terms: propSubtermReplace") (propSubtermReplace bigTerm [1,0]) ]

propSubtermReplace :: Ord a => Term a -> Position -> (Term a, Term a)
propSubtermReplace t p = (t,(t `replacePos` (t `atPos` p,p)))

bigTerm :: LNTerm
bigTerm = pair (pk (x1),
               expo (expo (inv x3,
                          x2 *: x4 *: f1 *: one *: inv (f3 *: f4) *: f3 *: f4 *: inv one),
                    inv (expo (x2,one)) *: f2))

normBigTerm :: LNTerm
normBigTerm = pair (pk (x1),expo (inv x3,mult [f1, f2, x4]))

tcompare :: MaudeHandle -> Test
tcompare hnd =
    TestLabel "Tests for variant order" $ TestList
      [ testTrue "a" (run $ isNormalInstance t su1 su2)
      , testTrue "b" $ not (run $ isNormalInstance t su1 su3)

      , testTrue "c" $ (run $ leqSubstVariant t su5 su4)
      , testTrue "d" $ not (run $ leqSubstVariant t su6 su4)

      , testEqual "e" (run $ compareSubstVariant t su4 su4) (Just EQ)
      , testEqual "f" (run $ compareSubstVariant t su5 su4) (Just LT)
      , testEqual "g" (run $ compareSubstVariant t su4 su5) (Just GT)
      , testEqual "h" (run $ compareSubstVariant t su6 su4) Nothing
      ]
  where
    run :: WithMaude a -> a
    run m = runReader m hnd
    t  = pair (inv (x1) *: x2, inv (x3) *: x2)
    su1 = substFromList [(lx1, x2)]
    su2 = substFromList [(lx2, p1)]
    su3 = substFromList [(lx3, x2)]
    su4 = substFromListVFresh [(lx1, x4), (lx2, x4)]
    su5 = substFromListVFresh [(lx1, p1), (lx2, p1)]
    su6 = substFromListVFresh [(lx1, x4), (lx2, x4), (lx3, x4)]

testsVariant :: MaudeHandle -> Test
testsVariant hnd =
    TestLabel "Tests for variant computation" $ TestList
      [ testEqual "a" (computeVariantsCheck (sdec (x1, p1)) `runReader` hnd)
                      (toSubsts [ []
                                , [(lx1, senc (x2, p1))] ])

      , testEqual "b" (computeVariantsCheck (x1  *:  p1) `runReader` hnd)
                      (toSubsts [ []
                                , [(lx1, x2 *: inv (p1))]
                                , [(lx1, inv (p1))]
                                , [(lx1, one)]
                                , [(lx1, x2 *:  inv (p1 *: x3))]
                                , [(lx1, inv (p1 *: x2))]
                                ])

      , testTrue "e" $ not (checkComplete (sdec (x1, p1)) (toSubsts [[]]) `runReader` hnd)
      , testTrue "f" $ (checkComplete (sdec (x1, p1)) (toSubsts [[], [(lx1, senc (x1,p1))]])
                        `runReader` hnd)
      ]
  where
    toSubsts = map substFromListVFresh

testsSimple :: MaudeHandle -> Test
testsSimple _hnd =
    TestLabel "Tests for simple functions" $ TestList
      [ testTrue "" (size [bigTerm] > 0) ]

-- | All unification infrastructure unit tests.
tests :: FilePath -> IO Test
tests maudePath = do
    mhnd <- startMaude maudePath allMaudeSig
    return $ TestList [ testsVariant mhnd
                      , tcompare mhnd
                      , testsSubs mhnd
                      , testsTerm
                      , testsSubst
                      , testsNorm mhnd
                      , testsUnify mhnd
                      , testAllHomomorphic mhnd
                      , testsSimple mhnd
                      , testsMatching mhnd
                      ]

-- | Maude signatures with all builtin symbols.
allMaudeSig :: MaudeSig
allMaudeSig = mconcat
    [ bpMaudeSig, msetMaudeSig -- do not add homMaudeSig
    , pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig, revealSignatureMaudeSig, hashMaudeSig ]


-- testing in ghci
----------------------------------------------------------------------------------

te :: LNTerm
te  = pair (inv (x1) *: x2, inv (x3) *: x2)

sub4, sub6 :: LNSubstVFresh
sub4 = substFromListVFresh [(lx1, x4), (lx2, x4)]
sub6 = substFromListVFresh [(lx1, x4), (lx2, x4), (lx3, x4)]

sub4', sub6' :: LNSubst
sub4' = freshToFreeAvoiding sub4 te
sub6' = freshToFreeAvoiding sub6 te

tevs :: [LVar]
tevs = frees te

runTest :: WithMaude a -> IO a
runTest m = do
    hnd <- startMaude "maude" allMaudeSig
    return $ m `runReader` hnd

{-

runTest $ matchLNTerm [ pair(xor [x5,x6],xor [x4,x5,x6]) `MatchWith` pair(x5,xor [x5,x4]) ]

should be matchable if next matchable also

runTest $ matchLNTerm [ pair(xor [x5,x6],xor [x4,x5,x6]) `MatchWith` pair(x5,xor [x5,x6]) ]

-}

-- convenience abbreviations
----------------------------------------------------------------------------------

pair, expo :: (Term a, Term a) -> Term a
expo = fAppExp
pair = fAppPair

inv :: Term a -> Term a
inv = fAppInv

union, mult :: Ord a => [Term a] -> Term a
union = fAppAC Union
mult  = fAppAC Mult

one :: Term a
one = fAppOne
