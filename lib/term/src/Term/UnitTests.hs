{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
-- |
-- Copyright   : (c) 2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
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
import Data.Bifunctor (second)

import Term.Unification.LPETerm
import Term.Unification.HomomorphicEncryption
import Term.Unification.UnificationCombinator

import qualified Term.Maude.Process as UM
import           System.IO.Unsafe (unsafePerformIO)

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

testAllHom :: MaudeHandle -> MaudeHandle -> Test
testAllHom _ mhndHom = TestLabel "All Homomorphic Tests" $
  TestList
    [ testsMatchingHom mhndHom mhndHom
    , testsUnifyHom mhndHom mhndHom
    , testsUnifyHomSf mhndHom mhndHom
    , testsUnifyHomRules mhndHom mhndHom
    , testUnifyCombSf mhndHom mhndHom
    , testPrinterHom mhndHom mhndHom
    ]

-- *****************************************************************************
-- Tests for Matching modulo EpsilonH (For Homomorphic encryption)
-- *****************************************************************************

-- match t p tries to find a substitution phi such that "t == phi applied to p"
testsMatchingHom :: MaudeHandle -> MaudeHandle -> Test
testsMatchingHom mhnd mhndHom = TestLabel "Tests for Matching modulo EpsilonH" $
  TestList $ map (\(testName, testOutcome, term1, term2) ->
    testMatchingHomWithPrint mhnd mhndHom testName testOutcome term1 term2)
    -- small examples
    [ ("a",                 True,   x0,            x0            )
    , ("b",                 True,   x1,            x0            )
    , ("c",                 True,   hpair (x1,x2),  x0            )
    , ("d",                 True,   hpair (x0,x2),  x0            )
    , ("e",                 False,  x0,            hpair (x0,x2)  )
    , ("f",                 True,   hpair (x0,x1),  hpair (x1,x2)  )
    , ("g",                 True,   hpair (x0,x1),  hpair (x1,x0)  )
    , ("h",                 True,   hpair (x1,x0),  hpair (x0,x1)  )
    -- bigger examples
    , ("homdef 1",           True,   henc (hpair (x0,x1), x2),                hpair (henc (x0,x2), henc (x1,x2))   )
    , ("homdef 2",           True,   hpair (henc (x0,x2), henc (x1,x2)),      henc (hpair (x0,x1), x2)             )
    , ("homdef1diffVars 1",  True,   henc (hpair (x0,x0), x0),                hpair (henc (x0,x2), henc (x1,x2))   )
    , ("homdef1diffVars 2",  False,  hpair (henc (x0,x2), henc (x1,x2)),      henc (hpair (x0,x0), x0)             )
    , ("hpair 1",            True,   hpair (hpair (x0,x0), x0),               hpair (hpair (x2,x3), x4)            )
    , ("hpair 2",            False,  hpair (hpair (x2,x3), x4),               hpair (hpair (x0,x0), x0)            )
    , ("hpair 3",            True,   hpair (hpair (x0,x1),hpair (x2,x3)),        hpair (hpair (x1,x2),hpair (x3,x4))     )
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
    -- Note: lnMatching will throw error so we don't test
    -- , ("node 3",            False,  node1,  x0      )
    ]

testMatchingHomWithPrint :: MaudeHandle -> MaudeHandle -> String -> Bool -> LNTerm -> LNTerm -> Test
testMatchingHomWithPrint mhnd mhndHom caseName caseOutcome t1 t2 =
  TestLabel caseName $ TestList [
      -- equal to expected outcome
      testTrue printText (caseOutcome == substHomMatches)
      -- terms equal after norming
    , testTrue "equal n" (caseOutcome == (t1N == t2NSubstH))
      -- if matching without homomorphic rules works then so should it with those rules
      -- lnMatches implies substHMatches
    , testTrue "ln=>hom" (not lnMatches || substHomMatches)
      -- comparing with the maude handle including homomorphic unification
    , testTrue "equal mhndHom" (caseOutcome == lnMatchesHom)
    -- lnMatches implies lnMatchesHom
    , testTrue "ln=>mhndHom" (not lnMatches || lnMatchesHom)
    -- checks that vars on the left are all orgVars
    , testTrue "isCorr match" (isCorrectMatchSubst (foldVarsVTerm [t1]) (foldVarsVTerm [t2]) directSubstHom)
    -- test correct sort
    , testTrue "correct sort match" (isSortCorrectSubst directSubstHom sortOfName)
  ]
  where
    printText = "------ TEST PRINTER ------" ++ "\n"
      ++ "Case:        " ++ caseName ++ "\n"
      ++ "Terms:       " ++ show t1 ++ ", " ++ show t2 ++ "\n"
      ++ "--- matchLNTerm ---" ++ "\n"
      ++ "NumMatchers: " ++ show numMatchers ++ "\n"
      ++ "Fst Matcher: " ++ show subst ++ "\n"
      ++ "New Terms:   " ++ show t1 ++ ", " ++ show t2Subst ++ "\n"
      ++ "--- matchHomLNTerm ---" ++ "\n"
      ++ "Did-Match    " ++ show substHomMatches ++ "\n"
      ++ "Matcher:     " ++ show directSubstHom ++ "\n"
      ++ "New Terms:   " ++ show t1 ++ ", " ++ show t2SubstH ++ "\n"
      ++ "--- with normed terms ---" ++ "\n"
      ++ "Terms:       " ++ show t1N ++ ", " ++ show t2N ++ "\n"
      ++ "New Terms:   " ++ show t1N ++ ", " ++ show t2NSubstH ++ "\n"
      ++ "------ END TEST PRINTER ------"
      ++ "Note: x.2 <~ x means x is being replaced by x.2" ++ "\n"

    t1N = normHom t1
    t2N = normHom t2

    substs = solveMatchLNTerm (t1 `matchWith` t2) `runReader` mhnd
    numMatchers = length substs
    lnMatches = not (null substs)
    subst = safeHead substs

    substsHom = solveMatchLNTerm (t1 `matchWith` t2) `runReader` mhndHom
    numMatchersHom = length substsHom
    lnMatchesHom = not (null substsHom)
    substHom = safeHead substsHom

    directSubstHomM = matchHomLTerm sortOfName (DelayedMatches [(t1N, t2N)])
    directSubstHom = if null directSubstHomM then emptySubst else head directSubstHomM
    substHomMatches = not (null directSubstHomM)

    t2Subst = applyVTerm subst t2
    t2SubstH = applyVTerm directSubstHom t2
    t2NSubstH = normHom $ applyVTerm directSubstHom t2N

    safeHead s = if null s then Subst $ M.fromList [(LVar "NOSUBST" LSortMsg 0,x0)] else head s

-- *****************************************************************************
-- Tests for Unification modulo EpsilonH (For Homomorphic encryption)
-- *****************************************************************************

-- Multiple tests for unification modulo EpisolonH algorithm 
-- implemented in unifyHomLNTerm
testsUnifyHom :: MaudeHandle -> MaudeHandle -> Test
testsUnifyHom mhnd mhndHom = TestLabel "Tests for Unify modulo EpsilonH" $
  TestList $ map (\(testName, testOutcome, term1, term2) ->
    testUnifyWithPrint mhnd mhndHom testName testOutcome term1 term2)
    [ ("1",         True,   x0,                                                               x0                                                                            )
    , ("doubleeq1", True,   pair (pair (x0,x2),pair (x2,x0)),                                    pair (pair (x2,x0),pair (x0,x2))                                                 )
    , ("doubleeq2", True,   pair (pair (x0,x0),x3),                                             pair (pair (pair (x2,x1),pair (x2,x1)),x2)                                        )
    , ("2",         True,   x0,                                                               x1                                                                            )
    , ("3",         False,  henc (x0,x1),                                                      x1                                                                            )
    , ("4",         True,   x0,                                                               henc (x1,x2)                                                                   )
    , ("5",         True,   henc ( hpair (x0,x1), x2),                                         x4                                                                            )
    , ("6",         True,   henc ( henc (hpair (x0,x1), x2),x0),                               henc (x5,x6)                                                                   )
    , ("7",         True,   hpair (x0,x0),                                                     hpair (x1,x2)                                                                  )
    , ("8",         True,   hpair (x0,x1),                                                     henc (x2,x3)                                                                   )
    , ("9",         True,   henc (x0,x1),                                                      hpair (x2,x3)                                                                  )
    , ("10",        True,   hpair (x0,x0),                                                     henc (x2,x3)                                                                   )
    , ("11",        True,   henc (x0,x1),                                                      hpair (x2,x2)                                                                  )
    , ("12",        False,  hpair (x0,x1),                                                     henc (x1,x3)                                                                   )
    , ("13",        False,  henc (x2,x1),                                                      hpair (x2,x3)                                                                  )
    , ("14",        True,   hpair (x0,x1),                                                     henc (x2,x2)                                                                   )
    , ("15",        True,   henc (x0,x0),                                                      hpair (x2,x3)                                                                  )
    , ("16",        False,  hpair (x0,x1),                                                     henc (x2,x0)                                                                   )
    , ("17",        False,  henc (x0,x2),                                                      hpair (x2,x3)                                                                  )
    , ("18",        True,   hpair (hpair (x0,x1),hpair (x2,x3)),                                 hpair (hpair (x1,x2),hpair (x3,x4))                                              )
    , ("19",        True,   hpair (hpair (x0,x1),hpair (x2,x3)),                                 hpair (hpair (x1,x2),hpair (x3,x0))                                              )
    , ("20",        True,   hpair (x0,x0),                                                     hpair (x1,hpair (x3,x2))                                                        )
    , ("21",        True,   hpair (x0,x0),                                                     hpair (hpair (x2,x3),hpair (hpair (x3,x3),x4))                                    )
    , ("22",        True,   hpair (x8,x8),                                                     hpair (hpair (henc (henc (x0,x1),x2),x3),henc (henc (henc (x4,x5),x6),x7))           )
    , ("defhenc 1", True,   henc ( hpair (x0,x1), x2),                                         hpair (henc (x0,x2), henc (x1,x2))                                            )
    , ("defhenc 2", True,   hpair ( henc (x0,x2), henc (x1,x2)),                               henc (hpair (x0,x1), x2)                                                      )
    , ("defhenc 3", True,   henc ( henc (hpair (x0,x1), x2),x0),                               henc (henc (hpair (x0,x1), x2),x0)                                             )
    , ("symEnc 1",  False,  senc ( hpair (x0,x1), x2),                                         hpair (senc (x0,x2), senc (x1,x2))                                            )
    , ("norm 1",    True,   hpair ( hpair (x0,x0), x0),                                        hpair (hpair (x2,x3), x4)                                                     )
    , ("norm 2",    True,   hpair ( hpair (x2,x3), x4),                                        hpair (hpair (x0,x0), x0)                                                     )
    , ("norm 3",    True,   henc ( hpair (x0,x0), x0),                                         hpair (henc (x1,x2), henc (x3,x4))                                            )
    , ("norm 4",    True,   henc ( hpair (x0,x0), x0),                                         hpair (henc (x1,x2), henc (x2,x4))                                            )
    , ("norm 5",    True,   henc ( hpair (x0,x1), x2),                                         henc (x3,x4)                                                                   )
    , ("norm 6",    True,   henc ( henc (hpair (x0,x1),x2),x3),hpair (henc (henc (x0,x2),x3),      henc (henc (x1,x2),x3))                                                         )
    , ("norm 7",    True,   henc ( hpair (henc (hpair (x0,x1),x2), hpair (henc (x3,x4),x5)), x6),  henc ( hpair (henc (hpair (x0,x1),x2), hpair (henc (x3,x4),x5)), x6)                )
    -- cases with different sorts
    , ("public 1",  True,   x0,            px0            )
    , ("public 2",  True,   px0,           x0             )
    , ("fresh 1",   True,   x0,            fx0            )
    , ("fresh 2",   True,   fx0,           x0             )
    , ("nat 1",     True,   x0,            nn1            )
    , ("nat 2",     True,   nn1,           x0             )
    , ("pubnat 1",  False,  px0,           nn1            )
    , ("pubnat 2",  False,  nn1,           px0            )
    , ("pubfr 1",   False,  px0,           fx0            )
    , ("pubfr 2",   False,  fx0,           px0            )
    , ("frnat 1",   False,  fx0,           nn1            )
    , ("frnat 2",   False,  nn1,           fx0            )
    , ("multi 1",   True,   hpair (x0,x1),  hpair (px0,px1) )
    , ("multi 2",   True,   hpair (x0,px0), hpair (px0,x0)  )
    , ("multi 3",   True,   hpair (x0,nn1), hpair (px0,x1)  )
    , ("samefr",    True,   fx0,           fx0            )
    , ("samenat",   True,   nn1,           nn1            )
    , ("samepub",   True,   px0,           px0            )
    , ("samefr 2",  True,   fx0,           fx1            )
    , ("samenat 2", True,   nn1,           nn2            )
    , ("samepub 2", True,   px0,           px1            )
    , ("difficult", False,  hpair (hpair (nn1,fx0),x2),     hpair (hpair (x2,x3),x3)  )
     -- timepoint cases
    , ("node 1",    True,   node1,         node1          )
    , ("node 2",    True,   node1,         node2          )
    -- Note: lnUnfify will throw error so we don't test
    -- , ("node 3",    False,  node1,        x0            )
    -- shaping and parsing
    , ("shapa 1",   True,   hpair(x0,x1),                    henc(x2,x3))
    , ("shapa 2",   True,   hpair(x0,x1),                    henc(henc(x2,x3),x4))
    , ("shapa 3",   True,   hpair(henc(x0,x1),x2),           henc(henc(x3,x4),x5))
    , ("shapa 4",   True,   hpair(henc(henc(x0,x1),x2),x3),  henc(henc(henc(x4,x5),x6),x7))
    , ("shapa 5",   True,   hpair(henc(x0,x1),x2),           henc(x3,x4))
    , ("shapa 6",   True,   hpair(henc(henc(x0,x1),x2),x3),  henc(x4,x5))
    , ("shapa 7",   True,   hpair(henc(henc(x0,x1),x2),x3),  henc(henc(x4,x5),x6))   
    -- TODO: 1 + 2 = 3 luege ob sorts
    -- Example womme müesst normhom awende nach einere rule application odr so
    ]

testUnifyWithPrint :: MaudeHandle -> MaudeHandle -> String -> Bool -> LNTerm -> LNTerm -> Test
testUnifyWithPrint mhnd mhndHom caseName caseOutcome t1 t2 =
  TestLabel caseName $ TestList [
    -- test if unification works as expected
      testTrue printText (caseOutcome == substHUnifies)
    -- normed terms equal after unification
    , testTrue "n equal" (caseOutcome == (t1NSubstH == t2NSubstH))
    -- freeToAvoid does not change the outcome
    , testTrue "freeAvoid" (caseOutcome == (t1NSubstHFreeAvoid == t2NSubstHFreeAvoid))
    -- if unifying without homomorphic rules works then so should it with those rules
    -- lnUnifies implies substHUnifies
    , testTrue "ln=>hom" (not lnUnifies || substHUnifies)
    -- multiples other tests if the unification was done correctly
    -- needs to be changed if unifyHomLTerm changes
    --, testTrue "isCorr substForm" (isCorrectPreSubst orgVars substForm)
    --, testTrue "isCorr freeAvoid" (isCorrectPreSubst orgVars substFormFreeAvoid)
    --, testTrue "isCorr freeAvoid 2" (isCorrectFreeAvoidSubst orgVars substForm substFormFreeAvoid)
    , testTrue "isCorr subst" (isCorrectSubst orgVars substH)
    -- test correct sort
    , testTrue "correct sort match" (isSortCorrectSubst substH sortOfName)
    -- test correct sort
    , testTrue "correct sort match" (isSortCorrectSubst substHomFreeAvoid sortOfName)
    -- tests with second maude handle
    , testTrue "equal mhndHom" (caseOutcome == lnUnifiesHom)
    , testTrue "ln=>mhndHom" (not lnUnifies || lnUnifiesHom)
    -- test norming function
    -- norming terms beforehand should not have any influence
    , testTrue "norm no influence 1" ((t1NSubstH == t2NSubstH) == (t1NSubstHN == t2NSubstH))
    , testTrue "norm no influence 2" ((t1NSubstH == t2NSubstH) == (t1NSubstH == t2NSubstHN))
    , testTrue "norm no influence 3" ((t1NSubstH == t2NSubstH) == (t1NSubstHN == t2NSubstHN))
    , testTrue "norm 1" (t1N == t1NN)
    , testTrue "norm 2" (t2N == t2NN)
  ]
  where
    printText = "------ TEST PRINTER ------" ++ "\n"
      ++ "Case:          " ++ caseName ++ "\n"
      ++ "Terms:         " ++ show t1 ++ ", " ++ show t2 ++ "\n"
      ++ "--- unifyLNTerm ---" ++ "\n"
      ++ "NumUnifiers:   " ++ show numUnifiers ++ "\n"
      ++ "First unifier: " ++ show subst ++ "\n"
      ++ "After fTFA:    VSubst: " ++ show substFreeAvoid ++ "\n"
      ++ "New Terms:     " ++ show t1SubstFreeAvoid ++ ", " ++ show t2SubstFreeAvoid ++ "\n"
      ++ "--- unifyHomLTerm ---" ++ "\n"
      ++ "First unifier: " ++ show substH ++ "\n"
      ++ "New Terms:     " ++ show t1SubstH ++ ", " ++ show t2SubstH ++ "\n"
      ++ "After fTFA:    VSubst: " ++ show substHFreeAvoid ++ "\n"
      ++ "New Terms:     " ++ show t1SubstHFreeAvoid ++ ", " ++ show t2SubstHFreeAvoid ++ "\n"
      ++ "--- with normed terms ---" ++ "\n"
      ++ "First unifier: " ++ show substH ++ "\n"
      ++ "New Terms:     " ++ show t1NSubstH ++ ", " ++ show t2NSubstH ++ "\n"
      ++ "After fTFA:    VSubst: " ++ show substHFreeAvoid ++ "\n"
      ++ "New Terms:     " ++ show t1NSubstHFreeAvoid ++ ", " ++ show t2NSubstHFreeAvoid ++ "\n"
      ++ "Note:          x.2 <~ x means x is being replaced by x.2" ++ "\n"
      ++ "------ END TEST PRINTER ------"

    substs = unifyLTerm sortOfName [Equal t1 t2] `runReader` mhnd
    numUnifiers = length substs
    subst = safeHead substs
    substFreeAvoid = freshToFreeAvoiding subst [t1,t2]
    lnUnifies = not (null substs)

    substsHom = unifyLTerm sortOfName [Equal t1 t2] `runReader` mhndHom
    numUnifiersHom = length substsHom
    substHom = safeHead substsHom
    substHomFreeAvoid = freshToFreeAvoiding substHom [t1,t2]
    lnUnifiesHom = not (null substsHom)

    substHUnifier = unifyHomLTerm sortOfName [Equal t1 t2]
    substH = if null substHUnifier then emptySubst else substFromList $ substToListVFresh (head substHUnifier)
    substHFreeAvoid = if null substHUnifier then emptySubst else freshToFreeAvoiding (head substHUnifier) [t1,t2]
    substHUnifies = not (null substHUnifier)

    orgVars = foldVarsVTerm [t1,t2]
    --unifier = unifyHomLTermWithVars sortOfName ([Equal t1 t2], orgVars)
    --substFormM = toSubstForm sortOfName orgVars =<< unifier
    --substForm = fromMaybe ([],[]) substFormM
    --substFormFreeAvoidM = toFreeAvoid orgVars =<< substFormM
    --substFormFreeAvoid = fromMaybe ([],[]) substFormFreeAvoidM

    t1SubstFreeAvoid = applyVTerm substFreeAvoid t1
    t2SubstFreeAvoid = applyVTerm substFreeAvoid t2

    t1SubstH = applyVTerm substH t1
    t2SubstH = applyVTerm substH t2
    t1SubstHFreeAvoid = applyVTerm substHFreeAvoid t1
    t2SubstHFreeAvoid = applyVTerm substHFreeAvoid t2

    t1NSubstH = normHom $ applyVTerm substH t1
    t2NSubstH = normHom $ applyVTerm substH t2
    t1NSubstHFreeAvoid = normHom $ applyVTerm substHFreeAvoid t1
    t2NSubstHFreeAvoid = normHom $ applyVTerm substHFreeAvoid t2

    t1N = normHom t1
    t2N = normHom t2
    t1NSubstHN = normHom $ applyVTerm substH t1N
    t2NSubstHN = normHom $ applyVTerm substH t2N

    t1NN = normHom t1N
    t2NN = normHom t2N

    safeHead s = if null s then SubstVFresh $ M.fromList [(LVar "NOSUBST" LSortMsg 0,x0)] else head s

-- *****************************************************************************
-- Functions to test if the substitution is correct
-- *****************************************************************************

isCorrectSubst :: IsConst c => [LVar] -> LSubst c -> Bool
isCorrectSubst orgVars subst = let s = substToList subst in
  allLeftVarsUnique s && allLeftVarsNotRight s && allLeftVarsOrgVars orgVars s && noOrgVarsRight orgVars s

isCorrectPreSubst :: IsConst c => [LVar] -> ([(LVar, LTerm c)], [LVar]) -> Bool
isCorrectPreSubst orgVars (s,_) =
  allLeftVarsUnique s && allLeftVarsNotRight s && allLeftVarsOrgVars orgVars s

isCorrectMatchSubst :: [LVar] -> [LVar] -> LSubst c -> Bool
isCorrectMatchSubst leftVars rightVars subst = let s = substToList subst in
  allLeftVarsOrgVars rightVars s && onlyOrgVarsRight leftVars s

isSortCorrectSubst :: IsConst c => LSubst c -> (c -> LSort) -> Bool
isSortCorrectSubst subst st = let s = substToList subst in all (\(v,t) -> sortCompare (lvarSort v) (sortOfLTerm st t) `elem` [Just EQ, Just GT]) s

isCorrectFreeAvoidSubst :: [LVar] -> ([(LVar, LTerm c)], [LVar]) -> ([(LVar, LTerm c)], [LVar]) -> Bool
isCorrectFreeAvoidSubst orgVars orgSubst completeSubst = let
  (cmpLVars, _) = second foldVarsVTerm $ unzip $ fst completeSubst
  (_, orgRVars) = second foldVarsVTerm $ unzip $ fst orgSubst
  in all (\v -> v `notElem` orgVars || v `elem` cmpLVars) orgRVars

allLeftVarsUnique :: [(LVar, a)] -> Bool
allLeftVarsUnique [] = True
allLeftVarsUnique ((vL,_):substs) = not (any (\(vR,_) -> vL == vR) substs) && allLeftVarsUnique substs

allLeftVarsNotRight :: [(LVar, LTerm c)] -> Bool
allLeftVarsNotRight subst = let (vars,terms) = unzip subst in not $ any (\v -> v `elem` foldVarsVTerm terms) vars

allLeftVarsOrgVars :: [LVar] -> [(LVar, LTerm c)] -> Bool
allLeftVarsOrgVars orgVars = all ((`elem` orgVars). fst)

noOrgVarsRight :: [LVar] -> [(LVar, LTerm c)] -> Bool
noOrgVarsRight orgVars subst = let rightVars = foldVarsVTerm (map snd subst) in all (`notElem` rightVars) orgVars

onlyOrgVarsRight :: [LVar] -> [(LVar, LTerm c)] -> Bool
onlyOrgVarsRight orgVars subst = let rightVars = foldVarsVTerm (map snd subst) in all (`elem` orgVars) rightVars

-- *****************************************************************************
-- Tests for Subfunctions of the Unification Algorithm modulo EpsilonH
-- *****************************************************************************

-- Multiple tests for the functions directly used by the 
-- homomorphic encrytion unification algorithm 
testsUnifyHomSf :: MaudeHandle -> MaudeHandle -> Test
testsUnifyHomSf mhnd _ =
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
    , testTrue "fromtoERep hpair" (fromERepresentation (buildERepresentation tP1) == tP1)
    , testTrue "fromtoERep henc" (fromERepresentation (buildERepresentation tH1) == tH1)
    , testTrue "fromtoPRep hpair" (fromPRepresentation (buildPRepresentation tP1) == tP1)
    , testTrue "fromtoPRep henc" (fromPRepresentation (buildPRepresentation tH1) == tH1)
    , testTrue "norm1" (normHom x0 == x0)
    , testTrue "norm2" (normHom (hpair (x0,x1)) == hpair (x0,x1))
    , testTrue "norm3" (normHom (henc (hpair (x0,x1),x2)) == hpair (henc (x0,x2),henc (x1,x2)))
    , testTrue "sanityCheck" (not (allLeftVarsNotRight [
        (LVar "x0" LSortMsg 15, hpair (varTerm $ LVar "x"  LSortMsg 22, varTerm $ LVar "x"  LSortMsg 23)),
        (LVar "x2" LSortMsg 17, varTerm $ LVar "x2" LSortMsg 21),
        (LVar "x"  LSortMsg 19, henc (varTerm $ LVar "x"  LSortMsg 22, varTerm $ LVar "x2" LSortMsg 21)),
        (LVar "x"  LSortMsg 20, henc (varTerm $ LVar "x"  LSortMsg 23, varTerm $ LVar "x2" LSortMsg 21)),
        (LVar "x"  LSortMsg 21, varTerm $ LVar "x"  LSortMsg 22),    -- x2 21 is on the right side
        (LVar "x"  LSortMsg 22, varTerm $ LVar "x"  LSortMsg 23) ])) -- x 22 is on the right side multiple times
    -- example:
    -- henc( henc( hpair(x0,x1), k0), k1) 
    -- -> henc( hpair( henc(x0,k0), henc(x1,k0) ), k1)
    -- -> hpair( henc(henc(x0,k0),k1) , henc(henc(x1,k0),k1) )
    , testTrue "norm4" (normHom norm1 == norm2)
    , testTrue "norm5" (normHom tpaper1 == tpaper1N)
    , testTrue "norm6" (normHom tpaper2 == tpaper2N)
    , testTrue "norm7" (normHom tpaper3 == tpaper3)
    , testTrue "norm8" (normHom normInKey == normedInKey)
    , tcn (hpair(x1,x2)) (hpair(x1,x2))
    , tcn (hpair(henc(x1,x3),henc(x2,x3))) (henc(hpair(x1,x2),x3)) 
    , tcn (hpair(henc(x1,x3),henc(x2,x3)) +: x4) (henc(hpair(x1,x2),x3) +: x4) 
    ]
  where
    tcn e1 e2 = testEqual ("norm "++ppLTerm e2) e1 (norm' e2 `runReader` mhnd)
    t1 = henc (hpair (x0,x1),x2)
    posT1 =
      [ ("", henc (hpair (x0,x1),x2) )
      , ("1", hpair (x0,x1) )
      , ("11", x0 )
      , ("12", x1 )
      , ("2", x2 ) ]
    t2 = hpair (henc (x0,x2),henc (x1,x2))
    posT2 =
      [ ("", hpair (henc (x0,x2),henc (x1,x2)) )
      , ("1", henc (x0,x2) )
      , ("11", x0 )
      , ("12", x2 )
      , ("2", henc (x1,x2) )
      , ("21", x1 )
      , ("22", x2 ) ]
    tpaper1 = hpair ( henc ( hpair (x0,x2), x4), x3 )
    tpaper1N = hpair ( hpair (henc (x0,x4),henc (x2,x4)), x3 )
    tpaper2 = hpair ( hpair (x0,x1), henc (hpair (x2,x3), x4))
    tpaper2N = hpair ( hpair (x0,x1), hpair (henc (x2,x4),henc (x3,x4)) )
    pPurePosTPaper2 =
      [ ("", tpaper2 )
      , ("1", hpair (x0,x1) )
      , ("11", x0 )
      , ("12", x1 )
      , ("2", henc (hpair (x2,x3),x4) ) ]
    maxPPurePosTPaper2 =
      [ ("11", x0 )
      , ("12", x1 )
      , ("2", henc (hpair (x2,x3),x4) ) ]
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
    norm1 = henc (henc (hpair (x0,x1),x2),x3)
    norm2 = hpair (henc (henc (x0,x2),x3), henc (henc (x1,x2),x3))
    normInKey = henc (x0,henc (hpair (x1,x2),x3))
    normedInKey = henc (x0,hpair (henc (x1,x3),henc (x2,x3)))
    tH1 = henc (x0, x1)
    tP1 = hpair (x0, x1)

-- *****************************************************************************
-- Tests for specific rules of the Homomorphic Unification Algorithm
-- *****************************************************************************

-- debugHomRule: 
--  [ failureOneHomRule             0
--  , failureTwoHomRule             1
--  , occurCheckHomRule             2
--  , clashHomRule                  3
--  , differentConsts               4
--  , doSortsCompare                5
--  , shapingHomRule                6
--  , parsingHomRule                7
--  , variableSubstitutionHomRule   8
--  , trivialHomRule                9
--  , stdDecompositionHomRule]      10
testsUnifyHomRules :: MaudeHandle -> MaudeHandle -> Test
testsUnifyHomRules _ _ = TestLabel "Tests for Unify module EpsilonH Rules" $
  TestList
    [ testTrue "trivial 1" (debugHomRule 9 tE1 s ([], vA [tE1]) == HEqs ([], []) )
    , testTrue "trivial 2" (debugHomRule 9 tFE1 s ([], vA [tFE1]) == HEqs ([], []) )
    , testTrue "trivial 3" (debugHomRule 9 tE2 s ([], vA [tE2]) == HNothing)
    , testTrue "std dec 1" (debugHomRule 10 tFE2 s ([], vA [tFE2]) == HEqs ([tE2, tE3], []) )
    , testTrue "std dec 2" (debugHomRule 10 tFE3 s ([], vA [tFE3]) == HNothing)
    , testTrue "var sub 1" (debugHomRule 8 tHE1 s ([], vA [tHE1]) == HNothing)
    , testTrue "var sub 2" (debugHomRule 8 tHE1 s ([tE3], vA [tHE1, tE3]) == HNothing)
    , testTrue "var sub 3" (debugHomRule 8 tHE1 s ([tE2], vA [tHE1, tE2]) == HSubstEqs tHE1S ([tHE1], []) )
    , testTrue "var sub 4" (debugHomRule 8 tHE1 s ([tFE2], vA [tHE1, tFE2]) == HSubstEqs tHE1S ([tHE1], []) )
    , testTrue "var sub 5" (debugHomRule 8 tE2 s ([tFE2], vA [tE2, tFE2]) == HSubstEqs tE2S ([tE2], []) )
    , testTrue "var sub 6" (debugHomRule 8 tHE2 s ([], vA [tHE2]) == HNothing)
    , testTrue "var sub 7" (debugHomRule 8 tHE2 s ([tE3], vA [tHE2, tE3]) == HNothing)
    , testTrue "var sub 8" (debugHomRule 8 tHE2 s ([tE2], vA [tHE2, tE2]) == HNothing)
    , testTrue "clash   1" (debugHomRule 3 tFE1 s ([], vA [tFE1]) == HNothing)
    , testTrue "clash   2" (debugHomRule 3 tFE3 s ([], vA [tFE3]) == HNothing)
    , testTrue "clash   3" (debugHomRule 3 tFE4 s ([], vA [tFE4]) == HFail)
    , testTrue "occur   1" (debugHomRule 2 tFE4 s ([], vA [tFE4]) == HNothing)
    , testTrue "occur   2" (debugHomRule 2 tE1 s ([], vA [tE1]) == HNothing)
    , testTrue "occur   3" (debugHomRule 2 tE2 s ([], vA [tE2]) == HNothing)
    , testTrue "occur   4" (debugHomRule 2 tHE1 s ([], vA [tHE1]) == HNothing)
    , testTrue "occur   5" (debugHomRule 2 tHE2 s ([], vA [tHE2]) == HFail)
    , testTrue "shaping 1" (debugHomRule 6 tFFE1 s ([], vA [tFFE1]) == HNothing) -- resolved by standard decomposition rule
    , testTrue "shaping 2" (debugHomRule 6 tFFE1 s ([tFFE2], vA [tFFE1, tFFE2]) == HNothing)
    , testTrue "shaping 3" (debugHomRule 6 tFE2 s ([], vA [tFE2]) == HNothing)
    , testTrue "shaping 4" (debugHomRule 6 tHE2 s ([], vA [tHE2]) == HNothing)
    , testTrue "shaping 5" (debugHomRule 6 tFFE4 s ([tFFE2], vA [tFFE4, tFFE2]) == HNothing)
    , testTrue "fail1   1" (debugHomRule 0 tFE5 s ([], vA [tFE5]) == HFail)
    , testTrue "fail1   2" (debugHomRule 0 tFE1 s ([], vA [tFE1]) == HNothing)
    , testTrue "fail1   3" (debugHomRule 0 tFFE1 s ([], vA [tFFE1]) == HNothing)
    , testTrue "fail1   4" (debugHomRule 0 tFE6 s ([], vA [tFE6]) == HNothing)
    , testTrue "fail2   1" (debugHomRule 1 tFFE5 s ([], vA [tFFE5]) == HFail)
    , testTrue "fail2   2" (debugHomRule 1 tFFE1 s ([], vA [tFFE1]) == HNothing)
    , testTrue "fail2   3" (debugHomRule 1 tE1 s ([], vA [tE1]) == HNothing)
    , testTrue "fail2   4" (debugHomRule 1 tFFE6 s ([], vA [tFFE6]) == HNothing)
    , testTrue "fail2   5" (debugHomRule 1 tFFE7 s ([], vA [tFFE7]) == HNothing)
    , testTrue "parsing 1" (debugHomRule 7 tFE1 s ([], vA [tFE1]) == HEqs ([tE1, tE4], []) )
    , testsUnifyHomShaping
    ]
  where
    tE1 = Equal (fH x0) (fH x0)
    tE2 = Equal (fH x0) (fH x2)
    tE3 = Equal (fH x1) (fH x3)
    tE4 = Equal (fH x1) (fH x1)
    tFE1 = Equal (fH (henc (x0,x1))) (fH (henc (x0,x1)))
    tFE2 = Equal (fH (henc (x0,x1))) (fH (henc (x2,x3)))
    tFE3 = Equal (fH (hpair (x0,x1))) (fH (henc (x2,x3)))
    tFE4 = Equal (fH (sdec (x0,x1))) (fH (henc (x2,x3)))
    tFE5 = Equal (fH (hpair (x0,x1))) (fH (henc (x0,x3))) -- out of phase on t5
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
    tFFE5 = Equal (fH (hpair (henc (hpair (x0,x1),x2),x3))) (fH (henc (henc (x4,x5),x6)))
    tFFE6 = Equal (fH (hpair (henc (x0,x2),x3))) (fH (henc (henc (x4,x5),x6)))
    tFFE7 = Equal (fH (hpair (henc (hpair (x0,x1),x2),x3))) (fH (henc (x4,x6)))
    s = sortOfName
    fH = toLPETerm
    vA = concatMap (varsVTerm . lTerm) . concatMap (\(Equal l r) -> [l,r])
    -- shaping:  tFFE1 = Equal P [""] [[x,x.1]] E [x.2,x.3,x.4] with n = 2, m = 2
    --    Return tFFE2 = Equal P [""] [[xH.1, x.3, x.1]] E [x.2,x.3,x.4]
    --           tFFE3 = Equal x.0                       E [xH.1, x.3]
    -- failure2: tFFE5 = Equal P ["1","2"] [[hpair(x,x.1),x.2],[x.3]] 
    --                         E [x.4,x.5,x.6] with n = 2, m = 1

testsUnifyHomShaping :: Test
testsUnifyHomShaping = TestLabel "Tests for Unify module EpsilonH Shaping Rule" $
  TestList
   [ testTrue "Shaping 1" (debugHomRule 6 pairHenc1 s ([], vA [pairHenc1]) == HEqs ([pairHenc1Shaped1, pairHenc1Shaped2], [sh1V]))
   , testTrue "Shaping 2" (debugHomRule 6 pairHenc2 s ([], vA [pairHenc2]) == HEqs ([pairHenc2Shaped1, pairHenc2Shaped2], [sh2V]))
   , testTrue "Shaping 3" (debugHomRule 6 pairHenc3 s ([], vA [pairHenc3]) == HEqs ([pairHenc3Shaped1, pairHenc3Shaped2], [sh3V]))
   , testTrue "Shaping 4" (debugHomRule 6 pairHenc4 s ([], vA [pairHenc4]) == HEqs ([pairHenc4Shaped1, pairHenc4Shaped2], [sh4V]))
   ]
  where
    -- example 1: n = 1, m = 2
    pairHenc1        = Equal (fH (hpair (x0,x1)))                    (fH (henc (x2,x3)))
    --                 P(E(x0),E(x1))                               E(x2,x3)
    --                 x = x0, km,..,kn = {}                        s = x2, k1' = kn' = x3
    --                 x' = sh1, k1',..,km-1' = x3
    --              -> P(..,E(sh1,x3),..)                           E(x2,x3)
    pairHenc1Shaped1 = Equal (fH (hpair (henc (sh1,x3),x1)))          (fH (henc (x2,x3)))
    --              -> x0                                           E(sh1,x3)
    pairHenc1Shaped2 = Equal (fH x0)                                (fH (henc (sh1,x3)))
    -- example 2: n = 2, m = 3
    pairHenc2        = Equal (fH (hpair (x0,x1)))                    (fH (henc (henc (x2,x3),x4)))
    --                 P(E(x0),E(x1))                               E(x2,x3,x4)
    --                 x = x0, km,..,kn = {}                        s = x2, k1',..,kn' = x3,x4
    --                 x' = sh2, k1',..,km-1' = x3,x4
    --              -> P(..,E(sh2,x3,x4),..)                        E(x2,x3,x4)
    pairHenc2Shaped1 = Equal (fH (hpair (henc (henc (sh2,x3),x4),x1))) (fH (henc (henc (x2,x3),x4)))
    --              -> x0                                           E(sh2,x3,x4)
    pairHenc2Shaped2 = Equal (fH x0)                                (fH (henc (henc (sh2,x3),x4)))
    -- example 3: n = 2, m = 2
    pairHenc3        = Equal (fH (hpair (henc (x0,x1),x2)))           (fH (henc (henc (x3,x4),x5)))
    --                 P(E(x0,x1),E(x2))                            E(x3,x4,x5)
    --                 x = x0, km,..,kn = x1                        s = x3, k1',..,kn' = x4,x5
    --                 x' = sh3, k1',..,km-1' = x4
    --              -> P(..,E(sh3,x4,x1),..)                        E(x3,x4,x5)
    pairHenc3Shaped1 = Equal (fH (hpair (henc (henc (sh3,x4),x1),x2))) (fH (henc (henc (x3,x4),x5)))
    --              -> x0                                           E(sh3,k4)
    pairHenc3Shaped2 = Equal (fH x0)                                (fH (henc (sh3,x4)))
    -- example 4: n = 3, m = 2
    pairHenc4        = Equal (fH (hpair (henc (henc (x0,x1),x2),x3)))  (fH (henc (henc (henc (x4,x5),x6),x7)))
    --                 P(E(x0,x1,x2),E(x3))                         E(x4,x5,x6,x7)
    --                 x = x0, km,..,kn = x1,x2                     s = x4, k1',..,kn' = x5,x6,x7
    --                 x' = sh4, k1',..,km-1' = x5
    --              -> P(..,E(sh4,x5,x1,x2),..)                     E(x4,x5,x6,x7)
    pairHenc4Shaped1 = Equal (fH (hpair (henc (henc (henc (sh4,x5),x1),x2),x3)))  (fH (henc (henc (henc (x4,x5),x6),x7)))
    --              -> x0                                           E(sh4,k4)
    pairHenc4Shaped2 = Equal (fH x0)                                (fH (henc (sh4,x5)))
    -- vars
    sh1V = LVar "sh" LSortMsg 4
    sh1 = varTerm sh1V
    sh2V = LVar "sh" LSortMsg 5
    sh2 = varTerm sh2V
    sh3V = LVar "sh" LSortMsg 6
    sh3 = varTerm sh3V
    sh4V = LVar "sh" LSortMsg 8
    sh4 = varTerm sh4V
    -- helper:
    s = sortOfName
    fH = toLPETerm
    vA = concatMap (varsVTerm . lTerm) . concatMap (\(Equal l r) -> [l,r])

testUnifyCombSf :: MaudeHandle -> MaudeHandle -> Test
testUnifyCombSf _ _ =
  TestLabel "Tests for Unify module EpsilonH subfunctions" $
  TestList
    [ testTrue "absvar   1" (abstractVars eg1 == eg1Abstracted)
    , testTrue "abseq    1" (abstractEqs eg1 == eg1) 
    , testTrue "splitsys 1" (splitSystem isRightSystem (fst eg1Abstracted) == eg1SplitSystem)
    ]
    where
      eg1 = ([Equal (henc(x1,x2) +: x3) (hpair(x4,x5) +: x3)], [lx 1,lx 2,lx 3,lx 4,lx 5])
      eg1Abstracted = (
        [ Equal (henc(x1,x2)) (varTerm $ labs 6),
          Equal (hpair(x4,x5)) (varTerm $ labs 7),
          Equal (varTerm (labs 6) +: x3) (varTerm (labs 7) +: x3)
        ], [labs 7, labs 6, lx 1,lx 2,lx 3,lx 4,lx 5])
      eg1SplitSystem = (
        [ Equal (varTerm (labs 6) +: x3) (varTerm (labs 7) +: x3)],
        [ Equal (henc(x1,x2)) (varTerm $ labs 6),
          Equal (hpair(x4,x5)) (varTerm $ labs 7) ] )
      lx = LVar "x" LSortMsg
      labs = LVar "abstractVar" LSortMsg
      isRightSystem :: IsConst c => Equal (LTerm c) -> Bool
      isRightSystem = isAnyHom . eqLHS

-- *****************************************************************************
-- Specific printer
-- *****************************************************************************

-- Test used to print return values and variables for debugging
-- Set Test return value to false to print out text
testPrinterHom :: MaudeHandle -> MaudeHandle -> Test
testPrinterHom mhnd _ =
  TestLabel "prints out debugging information" $
  TestList
    [ testTrue (show "") True]
  where
    eg1 = ([Equal (henc(x1,x2) +: x3) (hpair(x4,x5) +: x3)], [lx 1,lx 2,lx 3,lx 4,lx 5])
    lx = LVar "x" LSortMsg
    eg1SplitSystem = (
        [ Equal (varTerm (labs 6) +: x3) (varTerm (labs 7) +: x3)],
        [ Equal (henc(x1,x2)) (varTerm $ labs 6),
          Equal (hpair(x4,x5)) (varTerm $ labs 7) ] )
    absAllVars = [labs 7, labs 6, lx 1,lx 2,lx 3,lx 4,lx 5]
    labs = LVar "abstractVar" LSortMsg
    isRightSystem :: IsConst c => Equal (LTerm c) -> Bool
    isRightSystem = isAnyHom . eqLHS
    s = sortOfName
    acUnifier = unsafePerformIO . UM.unifyViaMaude mhnd (sortOfMConst sortOfName)
    homUnifier = unifyHomLTerm (sortOfMConst sortOfName)
    solvedSystems = solveDisjointSystems sortOfName
      eg1SplitSystem (acUnifier, homUnifier) (getAllPartitions absAllVars)
    -- (
      -- [[x.1,x.2,x.3,x.4,x.5],[abstractVar.6],[abstractVar.7]],
      -- [abstractVar.7,abstractVar.6,x.1],
      -- [(x.1,0),(abstractVar.6,0),(abstractVar.7,0)],
      -- [[(abstractVar.6,x.9),(abstractVar.7,x.9)]],
      -- [[(x.1,x.8),(abstractVar.6,henc(x.8,x.8)),(abstractVar.7,hpair(x.8,x.8))]]
    -- )
    cleanedSolvedSystem = cleanSolvedSystem absAllVars solvedSystems
    -- (
      -- [[x.1,x.2,x.3,x.4,x.5],[abstractVar.6],[abstractVar.7]],
      -- [abstractVar.7,abstractVar.6,x.1],
      -- [(x.1,0),(abstractVar.6,0),(abstractVar.7,0)],
      -- [[(abstractVar.6,x.9),(abstractVar.7,x.9)]],
      -- [[(x.1,x.12),(abstractVar.6,henc(x.12,x.12)),(abstractVar.7,hpair(x.12,x.12))]])
    --)
    combinedSolvedSystem = combineDisjointSystems cleanedSolvedSystem
    -- [VFresh: {x.12 <~ x.1, x.12 <~ x.2, x.12 <~ x.3, x.12 <~ x.4, 
    -- x.12 <~ x.5, x.9 <~ abstractVar.6, x.9 <~ abstractVar.7}]
    -- filteredCombinedSolvedSystem = filter (filterVailds (fst eg1)) $ concat combinedSolvedSystem

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
    mhnd    <- startMaude maudePath allMaudeSig
    mhndHom <- startMaude maudePath allMaudeSigPlusHom
    return $ TestList [ testsVariant mhnd
                      , tcompare mhnd
                      , testsSubs mhnd
                      , testsTerm
                      , testsSubst
                      , testsNorm mhnd
                      , testsUnify mhnd
                      , testAllHom mhnd mhndHom
                      , testsSimple mhnd
                      , testsMatching mhnd
                      ]

-- | Maude signatures with all builtin symbols.
allMaudeSig :: MaudeSig
allMaudeSig = mconcat
    [ bpMaudeSig, msetMaudeSig, xorMaudeSig -- do not add homMaudeSig
    , pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig, revealSignatureMaudeSig, hashMaudeSig ]

-- with enableHom=True
allMaudeSigPlusHom :: MaudeSig
allMaudeSigPlusHom = mconcat
    [ bpMaudeSig, msetMaudeSig, homMaudeSig, xorMaudeSig
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
