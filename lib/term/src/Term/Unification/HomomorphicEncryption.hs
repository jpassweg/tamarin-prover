{-# LANGUAGE LambdaCase #-}

module Term.Unification.HomomorphicEncryption (
  -- * Unification modulo EpsilonH for Homomorphic Encryption
  unifyHomomorphicLTermWrapper

  -- * Matching modulo EpsilonH for Homomorphic Encryption
  , matchHomomorphicLTermWrapper

  -- * Helper functions
  , eqsToTerms
  , foldVars
  , getNewSimilarVar

  -- * Failure rule Wrapper
  , failureHomomorphicRuleWrapper

  -- * For debugging
  , debugHomomorphicRule
  , HomomorphicRuleReturn(..)
  , unifyHomomorphicLTermWithVars
  , toSubstForm
  , toFreeAvoid

  , MConst(..)
  , toMConstA
  , toMConstC
  , toMConstVarList
  , fromMConst
  , sortOfMConst
) where

import Data.Maybe     (isJust, isNothing, mapMaybe, fromMaybe, maybeToList)
import Data.Bifunctor (first, second)

import Term.Unification.LPETerm
import Term.Unification.MConst

import Term.LTerm (
  LTerm, Lit(Var, Con), IsConst, LVar(..), TermView(FApp, Lit), LSort(..),
  isVar, varTerm, occursVTerm, varsVTerm, viewTerm,
  isHomPair, isHomEnc, sortCompare, sortOfLTerm)
-- Lit(Var, Con), IsConst, isVar, varTerm, termVar, varsVTerm, occursVTerm come from Term.VTerm
-- isHomPair, isHomEnc come from Term.Term
-- TermView(Lit, FApp), viewTerm, termViewToTerm come from Term.Term.Raw

import Term.Rewriting.Definitions (Equal(..), Match, flattenMatch)
import Term.Substitution.SubstVFree (LSubst, substFromList, applyVTerm)
import Term.Substitution.SubstVFresh (LSubstVFresh, substFromListVFresh)

import Extension.Prelude (sortednub)

-- Matching Algorithm using the Unification Algorithm
-----------------------------------------------------

matchHomomorphicLTermWrapper :: IsConst c => (c -> LSort) -> Match (LTerm c) -> [LSubst c]
matchHomomorphicLTermWrapper sortOf matchProblem = case flattenMatch matchProblem of
  Nothing -> []
  Just ms -> maybeToList $ matchHomomorphicLTerm sortOf ms

-- | matchHomomorphicLTerm
-- NOTE: Tamarin does allow matching pair(x0,x1) with pair(x1,x0) even though the substitution
-- x0 <~ x1, x1 <~ x0 is not allowed in unification.
-- NOTE: The variables orgVars are given to unifyHomomorphicLTermWithVars such that when 
-- creating new variables, unifyHomomorphicLTermWithVars can also take into account the 
-- variables that we turned into Consts in toMConstA.
-- NOTE: Id-substitutions (like x0 <~ x0) are being removed by the substFromList function.
matchHomomorphicLTerm :: IsConst c => (c -> LSort) -> [(LTerm c, LTerm c)] -> Maybe (LSubst c)
matchHomomorphicLTerm sortOf ms = let
  sO = sortOfMConst sortOf
  eqs = map (\(t,p) -> Equal (toMConstA t) (toMConstC p)) ms
  orgVars = foldVars $ foldr (\(t,p) vs -> t:p:vs) [] ms
  orgLVars = foldVars $ map snd ms
  unifier = unifyHomomorphicLTermWithVars sO (eqs, orgVars)
  in toSingleSubst =<< substFromMConst =<< toSubstForm sO orgLVars =<< unifier

-- Unification Algorithm Wrapper
--------------------------------

unifyHomomorphicLTermWrapper :: IsConst c =>  (c -> LSort) -> [Equal (LTerm c)] -> [LSubstVFresh c]
unifyHomomorphicLTermWrapper sortOf eqs = case unifyHomomorphicLTerm sortOf eqs of
    Just (_, hSF) -> [hSF]
    Nothing       -> []

unifyHomomorphicLTerm :: IsConst c => (c -> LSort) -> [Equal (LTerm c)] -> Maybe (LSubst c, LSubstVFresh c)
unifyHomomorphicLTerm sortOf eqs = let
  orgVars = foldVars $ eqsToTerms eqs
  unifier = unifyHomomorphicLTermWithVars sortOf (eqs, orgVars)
  in toDoubleSubst =<< toFreeAvoid orgVars =<< toSubstForm sortOf orgVars =<< unifier

-- Unification Algorithm using the Homomorphic Rules
----------------------------------------------------

-- | Types to make it easier to have an overview of the algorithm 
type PreSubst c = ([(LVar, LTerm c)], [LVar])
type EqsSubst a = ([Equal a], [LVar])

-- | @unifyHomomorphicLNTerm eqs@ returns a set of unifiers for @eqs@ modulo EpsilonH.
-- returns a substitution for terms so that they unify or an empty list 
-- if it is not possible to unify the terms
-- Types used:
-- LNTerm = Term (Lit (Con Name | Var LVar) | FApp FunSym [Term Lit ((Con Name | Var LVar))])
-- use viewTerm to use "case of" term
-- Equal LNTerm = Equal { eqLHS :: LNTerm, eqRHS :: LNTerm }
-- sortOfName :: Name -> LSort
-- data LSort = LSortPub | LSortFresh | LSortMsg | LSortNode -- Nodes are for dependency graphs
unifyHomomorphicLTermWithVars :: IsConst c => (c -> LSort) -> EqsSubst (LTerm c) -> Maybe (EqsSubst (LTerm c))
unifyHomomorphicLTermWithVars sortOf eqsSubst = let
  unifier = applyHomomorphicRules sortOf allHomomorphicRules $ first (map (fmap $ toLPETerm . normHomomorphic)) eqsSubst
  in Just . first (map (fmap lTerm)) =<< unifier

-- Applying Homomorphic Rules
-----------------------------

-- Type to translate HomorphicRuleReturn
data MaybeWFail a = MJust a | MNothing | MFail

-- | Applies all homomorphic rules given en block, i.e., 
-- it applies the first rule always first after each change
-- Holds for output: No equation is a duplicate of another equation
applyHomomorphicRules :: IsConst c => (c -> LSort) -> [HomomorphicRule c] -> EqsSubst (LPETerm c) -> Maybe (EqsSubst (LPETerm c))
applyHomomorphicRules _ [] eqsSubst = Just eqsSubst -- no more rules to apply 
applyHomomorphicRules sortOf (rule:rules) eqsSubst =
  case applyHomomorphicRule sortOf rule eqsSubst [] of
    MJust newEqsSubst -> applyHomomorphicRules sortOf allHomomorphicRules newEqsSubst
    MNothing          -> applyHomomorphicRules sortOf rules eqsSubst
    MFail             -> Nothing

-- | Applies the homomorphic rule to the first term possible in equation list or returns Nothing 
-- if the rule is not applicable to any terms
applyHomomorphicRule :: IsConst c => (c -> LSort) -> HomomorphicRule c -> EqsSubst (LPETerm c) -> [Equal (LPETerm c)] -> MaybeWFail (EqsSubst (LPETerm c))
applyHomomorphicRule _ _ ([], _) _ = MNothing
applyHomomorphicRule sortOf rule (e:es, allVars) passedEqs = let eqsSubst = (es ++ passedEqs, allVars) in
  case rule e sortOf eqsSubst of
    HEqs            newSubst -> MJust $ combineAnySubst eqsSubst newSubst
    HSubstEqs subst newSubst -> MJust $ combineAnySubst (applyEqsSubst subst eqsSubst) newSubst
    HNothing                 -> applyHomomorphicRule sortOf rule (es, allVars) (e:passedEqs)
    HFail                    -> MFail
  where
    applyEqsSubst :: IsConst c => [(LVar, LTerm c)] -> EqsSubst (LPETerm c) -> EqsSubst (LPETerm c)
    applyEqsSubst subst = first (map (fmap (toLPETerm . normHomomorphic . applyVTerm (substFromList subst) . lTerm)))

-- | To Homomorphic Solved Form (EqsSubst to PreSubst)
------------------------------------------------------

-- This function also filters out all equations, for which the correpsonding substitution has a variable on the left side, 
-- that is not part of original Variables (Note that for matching, are only the variables in p), as otherwise, it was 
-- tested that the EquationStore will at some point have a substitution for which dom and vrange coincide in that variable.  
toSubstForm :: IsConst c => (c -> LSort) -> [LVar] -> EqsSubst (LTerm c) -> Maybe (PreSubst c)
toSubstForm sortOf orgVars (eqs, allVars) = let
  substWODubVars = map (moveVarLeft sortOf orgVars) $ filter (not . dubVars) eqs
  substM         = addOrderDubVars orgVars (unzip $ catMaybesWFail substWODubVars) $ getDubVars eqs
  subst          = fromMaybe [] substM
  in if not (any isMFail substWODubVars) && isJust substM then Just (subst, allVars) else Nothing

moveVarLeft :: IsConst c => (c -> LSort) -> [LVar] -> Equal (LTerm c) -> MaybeWFail (LVar, LTerm c)
moveVarLeft sortOf orgVars (Equal l r) = case (viewTerm l, viewTerm r) of
  (Lit (Var lv), Lit (Var rv)) | lvarSort lv == lvarSort rv                           -> MFail -- should have been filtered out
  (Lit (Var lv), Lit (Var rv)) | sortCompare (lvarSort lv) (lvarSort rv) == Just GT
                                 && lv `elem` orgVars                                 -> MJust (lv, r)
  (Lit (Var lv), Lit (Var rv)) | sortCompare (lvarSort lv) (lvarSort rv) == Just GT   -> MNothing
  (Lit (Var lv), Lit (Var rv)) | sortCompare (lvarSort lv) (lvarSort rv) == Just LT
                                 && rv `elem` orgVars                                 -> MJust (rv, l)
  (Lit (Var lv), Lit (Var rv)) | sortCompare (lvarSort lv) (lvarSort rv) == Just LT   -> MNothing
  (Lit (Var lv), Lit (Var rv)) | isNothing $ sortCompare (lvarSort lv) (lvarSort rv)  -> MFail -- Uncomparable sorts should have been caught
  (Lit (Var lv), _           ) | sortCorrectForSubst sortOf lv r && lv `elem` orgVars -> MJust (lv, r)
  (Lit (Var lv), _           ) | sortCorrectForSubst sortOf lv r                      -> MNothing
  (Lit (Var _ ), _           )                                                        -> MFail -- Uncomparable sorts should have been caught
  (_,            Lit (Var rv)) | sortCorrectForSubst sortOf rv l && rv `elem` orgVars -> MJust (rv, l)
  (_,            Lit (Var rv)) | sortCorrectForSubst sortOf rv l                      -> MNothing
  (_,            Lit (Var _ ))                                                        -> MFail -- Uncomparable sorts should have been caught
  (Lit (Con cl), Lit (Con cr)) | cl == cr                                             -> MFail -- Equal consts should have dissapeared
  (Lit (Con _ ), Lit (Con _ ))                                                        -> MFail -- Unequal consts should have been caught
  (Lit (Con _ ), _           )                                                        -> MFail -- Const to Term not possible
  (_,            Lit (Con _ ))                                                        -> MFail -- Const to Term not possible
  (FApp fl _,    FApp fr _   ) | fl == fr                                             -> MFail -- Same functions not possible
  (FApp _  _,    FApp _  _   )                                                        -> MFail -- Different function symbols not allowed

addOrderDubVars :: IsConst c => [LVar] -> ([LVar], [LTerm c]) -> [(LVar, LVar)] -> Maybe [(LVar, LTerm c)]
addOrderDubVars _ subst [] = Just (uncurry zip subst)
addOrderDubVars orgVars (lPVars, rPTerms) ((lv,rv):dvs) = let
  rPVars = foldVars rPTerms
  vs = foldr (\(l,r) s -> l:r:s) [] dvs
  in case (lv `elem` lPVars, lv `elem` rPVars, lv `elem` orgVars, lv `elem` vs, rv `elem` lPVars, rv `elem` rPVars, rv `elem` orgVars, rv `elem` vs) of
    (_,    _,    False,_,      _,    _,    False,_    ) -> addOrderDubVars orgVars (lPVars, rPTerms) dvs
    (True, True, _,    _,      _,    _,    _,    _    ) -> Nothing -- left var also on right side
    (_,    _,    _,    _,      True, True, _,    _    ) -> Nothing -- left var also on right side
    (True, False,_,    _,      False,True, _,    _    ) -> Nothing -- duplicate rule or left var also on right side
    (False,True, _,    _,      True, False,_,    _    ) -> Nothing -- duplicate rule or left var also on right side
    (True, False,_,    _,      True, False,_,    _    ) -> if getRightTerm lv == getRightTerm rv
                                                           then addOrderDubVars orgVars (lPVars, rPTerms) dvs
                                                           else Nothing -- orderDubVars error
    (False,True, _,    _,      False,True, _,    _    ) -> Nothing -- seems like var sub was not applied correctly
    (True, False,_,    _,      False,False,True, _    ) -> addOrderDubVars orgVars (rv:lPVars, getRightTerm lv:rPTerms) dvs
    (True, False,_,    _,      False,False,False,_    ) -> addOrderDubVars orgVars (lPVars, rPTerms) dvs
    (False,False,True, _,      True, False,_,    _    ) -> addOrderDubVars orgVars (lv:lPVars, getRightTerm rv:rPTerms) dvs
    (False,False,False,_,      True, False,_,    _    ) -> addOrderDubVars orgVars (lPVars, rPTerms) dvs
    (False,True, _,    _,      False,False,True, _    ) -> addOrderDubVars orgVars (rv:lPVars, varTerm lv:rPTerms) dvs
    (False,True, _,    _,      False,False,False,_    ) -> addOrderDubVars orgVars (lPVars, rPTerms) dvs
    (False,False,True, _,      False,True, _,    _    ) -> addOrderDubVars orgVars (lv:lPVars, varTerm rv:rPTerms) dvs
    (False,False,False,_,      False,True, _,    _    ) -> addOrderDubVars orgVars (lPVars, rPTerms) dvs
    (False,False,True, False,  False,False,False,_    ) -> addOrderDubVars orgVars (lv:lPVars, varTerm rv:rPTerms) dvs
    (False,False,False,_,      False,False,True, False) -> addOrderDubVars orgVars (rv:lPVars, varTerm lv:rPTerms) dvs
    (False,False,True, False,  False,False,True, True ) -> addOrderDubVars orgVars (lv:lPVars, varTerm rv:rPTerms) dvs
    (False,False,True, True,   False,False,True, False) -> addOrderDubVars orgVars (rv:lPVars, varTerm lv:rPTerms) dvs
    (False,False,True, True,   False,False,False,_    ) -> addOrderDubVars orgVars (lv:lPVars, varTerm rv:rPTerms) dvs
    (False,False,False,_,      False,False,True, True ) -> addOrderDubVars orgVars (rv:lPVars, varTerm lv:rPTerms) dvs
    -- Symmetric cases can not be solved ideally
    (False,False,True, False,  False,False,True, False) -> addOrderDubVars orgVars (lv:lPVars, varTerm rv:rPTerms) dvs
    (False,False,True, True,   False,False,True, True ) -> addOrderDubVars orgVars (lv:lPVars, varTerm rv:rPTerms) dvs
  where
    getRightTerm v = snd $ head $ filter (\s -> fst s == v) (zip lPVars rPTerms)

-- To Free Avoid
----------------

toFreeAvoid :: IsConst c => [LVar] -> PreSubst c -> Maybe (PreSubst c)
toFreeAvoid orgVars subst = let
  freeAvoidingSubst = getFreeAvoidingSubstOfTerms orgVars ([], snd subst) (map snd (fst subst))
  completeSubst = combineAnySubst freeAvoidingSubst (applyPreSubstToVrange freeAvoidingSubst subst)
  in Just completeSubst
  where
    applyPreSubstToVrange :: IsConst c => PreSubst c -> PreSubst c -> PreSubst c
    applyPreSubstToVrange fstSubst = first (map (second (applyVTerm (substFromList (fst fstSubst)))))

getFreeAvoidingSubstOfTerms :: [LVar] -> PreSubst c -> [LTerm c] -> PreSubst c
getFreeAvoidingSubstOfTerms orgVars = foldl (getFreeAvoidingSubstOfTerm orgVars)

getFreeAvoidingSubstOfTerm :: [LVar] -> PreSubst c -> LTerm c -> PreSubst c
getFreeAvoidingSubstOfTerm orgVars (newSubst, allVs) t =
  case viewTerm t of
    (Lit (Con _)) -> (newSubst, allVs)
    (Lit (Var x)) ->
      if x `elem` map fst newSubst || x `notElem` orgVars
      then (newSubst, allVs)
      else let newV = getNewSimilarVar x allVs in ((x, varTerm newV):newSubst, newV:allVs)
    (FApp _ args) -> getFreeAvoidingSubstOfTerms orgVars (newSubst, allVs) args

-- Presubst to Substitution
---------------------------

toDoubleSubst :: PreSubst c -> Maybe (LSubst c, LSubstVFresh c)
toDoubleSubst = Just . (\s -> (substFromList s, substFromListVFresh s)) . fst

toSingleSubst :: PreSubst c -> Maybe (LSubst c)
toSingleSubst = Just . substFromList . fst

-- Homomorphic Rules Managers
-----------------------------

-- | Return type for a HomomorphicRule
data HomomorphicRuleReturn c =
    HEqs                        (EqsSubst (LPETerm c))
  | HSubstEqs [(LVar, LTerm c)] (EqsSubst (LPETerm c))
  | HNothing
  | HFail
  deriving (Show, Eq)

-- | Type for rules applied to equations for unification modulo EpsilonH
-- @arg1 = equation which we try to apply the rule on
-- @arg2 = translation from terms to sorts
-- @arg3 = all other equations (may be needed to check if a variable occurs in them)
type HomomorphicRule c = Equal (LPETerm c) -> (c -> LSort) -> EqsSubst (LPETerm c) -> HomomorphicRuleReturn c

-- | All homomorphic rules in order of application
-- All rules are added as such that they are first applied on the equation
-- Equal (eqLHS eq) (eqRHS eq) and then on the equation Equal (eqRHS eq) (eqLHS eq)
-- with eq being the first argument given to the function
allHomomorphicRules :: IsConst c => [HomomorphicRule c]
allHomomorphicRules = map (\r -> combineWrapperHomomorphicRule r (switchedWrapperHomomorphicRule r))
  -- failure rules first
  [ failureOneHomomorphicRule
  , failureTwoHomomorphicRule
  , occurCheckHomomorphicRule
  , clashHomomorphicRule
  -- new failure rules
  , differentConsts
  , doSortsCompare
  -- then homomorphic patterns   
  -- shaping best before parsing  
  , shapingHomomorphicRule
  , parsingHomomorphicRule
  -- varSub en block with homorphic patterns
  , variableSubstitutionHomomorphicRule
  -- then other rules
  , trivialHomomorphicRule
  , stdDecompositionHomomorphicRule ]

-- | Combines two rules and runs the second rule if first returns HNothing
combineWrapperHomomorphicRule :: IsConst c => HomomorphicRule c -> HomomorphicRule c -> HomomorphicRule c
combineWrapperHomomorphicRule rule1 rule2 eq sortOf eqsSubst =
  case rule1 eq sortOf eqsSubst of
    HNothing -> rule2 eq sortOf eqsSubst
    ret      -> ret

-- | Since the equality sign used is not oriented, we need
-- to look at the possibility of rule applications for 
-- both x = t and t = x for any equation.
-- This function is used in combination with combineWrapperHomomorphicRule
switchedWrapperHomomorphicRule :: IsConst c => HomomorphicRule c -> HomomorphicRule c
switchedWrapperHomomorphicRule rule eq = rule (Equal (eqRHS eq) (eqLHS eq))

-- | used to export homomorphic rules for debugging
debugHomomorphicRule :: IsConst c => Int -> HomomorphicRule c
debugHomomorphicRule i = allHomomorphicRules !! i

-- | Standard syntactic inference rules
-----------------------------------------

trivialHomomorphicRule :: IsConst c => HomomorphicRule c
trivialHomomorphicRule (Equal eL eR) _ _ = if lTerm eL == lTerm eR then HEqs ([],[]) else HNothing

stdDecompositionHomomorphicRule :: IsConst c => HomomorphicRule c
stdDecompositionHomomorphicRule (Equal eL eR) _ _ =
  case (viewTermPE eL, viewTermPE eR) of
    (FApp lfsym largs, FApp rfsym rargs) | lfsym == rfsym && length largs == length rargs 
      -> HEqs (zipWith (\l r -> Equal (toLPETerm l) (toLPETerm r)) largs rargs, [])
    _ -> HNothing

variableSubstitutionHomomorphicRule :: IsConst c => HomomorphicRule c
variableSubstitutionHomomorphicRule (Equal eL eR) sortOf (eqs,_) = let tR = lTerm eR in
  case (viewTermPE eL, viewTermPE eR) of
    (Lit (Var vl), Lit (Var vr)) | lvarSort vl == lvarSort vr ->
      if vl /= vr && occursVTermEqs vl eqs && occursVTermEqs vr eqs
      then HSubstEqs [(vl, tR)] ([Equal eL eR],[])
      else HNothing
    (Lit (Var vl), _) ->
      if not (occursVTerm vl tR) && occursVTermEqs vl eqs && sortCorrectForSubst sortOf vl tR
      then HSubstEqs [(vl, tR)] ([Equal eL eR],[])
      else HNothing
    _ -> HNothing

clashHomomorphicRule :: IsConst c => HomomorphicRule c
clashHomomorphicRule (Equal eL eR) _ _ = let tL = lTerm eL; tR = lTerm eR
  in case (viewTermPE eL, viewTermPE eR) of
    (FApp lfsym _, FApp rfsym _) | lfsym /= rfsym && not (isHomPair tL && isHomEnc tR) && not (isHomEnc tL && isHomPair tR)
      -> HFail
    _ -> HNothing

occurCheckHomomorphicRule :: IsConst c => HomomorphicRule c
occurCheckHomomorphicRule (Equal tL tR) _ _ = case viewTermPE tL of
    (Lit (Var vL)) | tL /= tR && occursVTerm vL (lTerm tR) -> HFail
    _                                                      -> HNothing

-- | Newly added rules for incompatible sorts
---------------------------------------------

-- Checks if consts can be unified
differentConsts :: IsConst c => HomomorphicRule c
differentConsts (Equal eL eR) _ _ = case (viewTermPE eL, viewTermPE eR) of
  (Lit (Con cl), Lit (Con cr)) -> if cl == cr then HNothing else HFail
  (Lit (Con _ ), Lit (Var _ )) -> HNothing
  (Lit (Con _ ), _           ) -> HFail
  (Lit (Var _ ), Lit (Con _ )) -> HNothing
  (_,            Lit (Con _ )) -> HFail
  _                            -> HNothing

-- Checks if sorts are incompatible
doSortsCompare :: IsConst c => HomomorphicRule c
doSortsCompare (Equal eL eR) sortOf _ = case (viewTermPE eL, viewTermPE eR) of
  (Lit (Var vl), Lit (Var vr)) -> 
    if sortCorrectForSubst sortOf vl (lTerm eR) || sortCorrectForSubst sortOf vr (lTerm eL) then HNothing else HFail
  (Lit (Var vl), _           ) -> 
    if sortCorrectForSubst sortOf vl (lTerm eR) then HNothing else HFail
  (_,            Lit (Var vr)) -> 
    if sortCorrectForSubst sortOf vr (lTerm eL) then HNothing else HFail
  _                            -> 
    if isJust $ sortCompare (sortOfLTerm sortOf $ lTerm eL) (sortOfLTerm sortOf $ lTerm eR) then HNothing else HFail

-- | Homomorphic Patterns
-------------------------

shapingHomomorphicRule :: IsConst c => HomomorphicRule c
shapingHomomorphicRule (Equal eL eR) _ (_, allVars) = let
  eRepsLHS = eRepsTerms $ pRep eL
  n = length (eRep eR) - 1
  in if length eRepsLHS > 1 && n >= 1
  then case findQualifyingETerm eRepsLHS n 0 of
    Just (qualifyingIndex, qualifyingELhs, x) -> let
      m = n + 2 - length qualifyingELhs
      xFresh = getNewSimilarVar (LVar "sh" LSortMsg 0) allVars
      lhs1NewPTerm = let (ys,zs) = splitAt qualifyingIndex eRepsLHS in
        PRep (eRepsString $ pRep eL) 
        (ys ++ [[varTerm xFresh] ++ take (m-1) (tail (eRep eR)) ++ tail qualifyingELhs] ++ tail zs)
      lhs1 = toLPETerm $ normHomomorphic $ fromPRepresentation lhs1NewPTerm
      rhs2 = toLPETerm $ normHomomorphic $ fromERepresentation $ varTerm xFresh : take (m-1) (tail (eRep eR))
      in HEqs ([Equal lhs1 eR, Equal (toLPETerm $ varTerm x) rhs2], [xFresh])
    Nothing -> HNothing
  else HNothing
  where
    findQualifyingETerm :: IsConst c => [ERepresentation c] -> Int -> Int -> Maybe (Int, ERepresentation c, LVar)
    findQualifyingETerm [] _ _ = Nothing
    findQualifyingETerm (e:es) n ind = case viewTerm (head e) of
      (Lit (Var v)) | (length e - 1 < n) && not (null e) -> Just (ind, e, v)
      _                                                  -> findQualifyingETerm es n (ind+1)

failureOneHomomorphicRule :: IsConst c => HomomorphicRule c
failureOneHomomorphicRule (Equal eL eR) _ _ = let
    (tL, tR) = (lTerm eL, lTerm eR)
    tLNonKey = filter (\(p,_) -> all ('1' ==) (ePosition p tL)) (positionsWithTerms tL)
    tRNonKey = filter (\(p,_) -> all ('1' ==) (ePosition p tR)) (positionsWithTerms tR)
  in if any (\(mL,mR) -> positionsIncompatible mL tL mR tR) (matchVars tLNonKey tRNonKey)
  then HFail
  else HNothing
  where
    matchVars :: IsConst c => [(String, LTerm c)] -> [(String, LTerm c)] -> [(String, String)]
    matchVars [] _ = []
    matchVars (v:vs) vs2 =
      let matches = filter (\vv2 -> snd v == snd vv2) vs2 in
      if isVar (snd v) && not (null matches)
      then map (\(m,_) -> (fst v, m)) matches ++ matchVars vs vs2
      else matchVars vs vs2

failureTwoHomomorphicRule :: IsConst c => HomomorphicRule c
failureTwoHomomorphicRule (Equal eL eR) _ _ = let eRepsLHS = eRepsTerms $ pRep eL in 
  if any (\e -> not (isVar $ head e) && (length e < length (eRep eR))) eRepsLHS && length eRepsLHS > 1 
  then HFail
  else HNothing

failureHomomorphicRuleWrapper :: IsConst c => LTerm c -> LTerm c -> Bool
failureHomomorphicRuleWrapper l r = let
    lPE = toLPETerm $ normHomomorphic l
    rPE = toLPETerm $ normHomomorphic r
  in case ( failureOneHomomorphicRule (Equal lPE rPE) (const LSortMsg) ([], []),
            failureTwoHomomorphicRule (Equal lPE rPE) (const LSortMsg) ([], [])
          ) of
    (HNothing, HNothing) -> True
    _ -> False

parsingHomomorphicRule :: IsConst c => HomomorphicRule c
parsingHomomorphicRule (Equal eL eR) _ _ = let
  eRepsLHS = eRepsTerms $ pRep eL
  newLHS = toLPETerm $ normHomomorphic $ fromPRepresentation $ PRep (eRepsString $ pRep eL) (map init eRepsLHS)
  newRHS = toLPETerm $ normHomomorphic $ fromERepresentation $ init (eRep eR)
  allKms = map (toLPETerm . normHomomorphic) $ last (eRep eR) : map last eRepsLHS
  in if all (\t -> length t >= 2) (eRepsLHS ++ [eRep eR])
  then HEqs (Equal newLHS newRHS : getAllCombinations allKms, [])
  else HNothing
  where
    getAllCombinations :: IsConst c => [LPETerm c] -> [Equal (LPETerm c)]
    getAllCombinations [] = []
    getAllCombinations (x:xs) = map (Equal x) xs ++ getAllCombinations xs

-- | Helper functions
---------------------

-- | @sortGreaterEq v t@ returns @True@ if the sort ensures that the sort of @v@ is greater or equal to
--   the sort of @t@.
sortCorrectForSubst :: IsConst c => (c -> LSort) -> LVar -> LTerm c -> Bool
sortCorrectForSubst st v t = sortCompare (lvarSort v) (sortOfLTerm st t) `elem` [Just EQ, Just GT]

eqsToTerms :: [Equal a] -> [a]
eqsToTerms [] = []
eqsToTerms (e:es) = eqLHS e : eqRHS e : eqsToTerms es

foldVars :: [LTerm c] -> [LVar]
foldVars = sortednub . concatMap varsVTerm

getNewSimilarVar :: LVar -> [LVar] -> LVar
getNewSimilarVar x allVars = LVar (lvarName x) (lvarSort x) $ (+) 1 $ foldr (max . lvarIdx) (lvarIdx x) allVars

occursVTermEqs :: LVar -> [Equal (LPETerm c)] -> Bool
occursVTermEqs v eqs = any (occursVTerm v . lTerm) (eqsToTerms eqs)

dubVars :: Equal (LTerm c) -> Bool
dubVars (Equal l r) = case (viewTerm l, viewTerm r) of
  (Lit (Var lv), Lit (Var rv)) | lvarSort lv == lvarSort rv -> True
  _                                                         -> False

getDubVars :: [Equal (LTerm c)] -> [(LVar, LVar)]
getDubVars [] = []
getDubVars (Equal l r:es) = case (viewTerm l, viewTerm r) of
  (Lit (Var lv), Lit (Var rv)) | lvarSort lv == lvarSort rv -> (lv,rv):getDubVars es
  _                                                         -> getDubVars es

substFromMConst :: IsConst c => PreSubst (MConst c) -> Maybe (PreSubst c)
substFromMConst = Just . first (map (second fromMConst))

combineAnySubst :: Ord b => ([a],[b]) -> ([a],[b]) -> ([a],[b])
combineAnySubst (es1,vs1) (es2,vs2) = (es1++es2, sortednub (vs1++vs2))

catMaybesWFail :: [MaybeWFail a] -> [a]
catMaybesWFail = mapMaybe (\case MJust s -> Just s; _ -> Nothing)

isMFail :: MaybeWFail a -> Bool
isMFail = \case MFail -> True; _ -> False