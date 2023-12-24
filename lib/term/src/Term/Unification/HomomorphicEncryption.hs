
module Term.Unification.HomomorphicEncryption (
  -- * Unification modulo EpsilonH for Homomorphic Encryption
  unifyHomLTerm

  -- * Matching modulo EpsilonH for Homomorphic Encryption
  , matchHomLTerm

  -- * Failure rule Wrapper
  , fastTestUnifiableHom

  -- * For debugging
  , debugHomRule
  , HomRuleReturn(..)

  -- * Convenience export
  , sortOfMConst
) where

import Data.Maybe     (isJust, isNothing, fromMaybe, catMaybes)
import Data.Either    (partitionEithers)
import Data.Bifunctor (first, second)
import Data.List      (nub)

import Term.Unification.LPETerm
import Term.Unification.MConst

import Term.LTerm (
  LTerm, Lit(Var, Con), IsConst, LVar(..), TermView(FApp, Lit), LSort(..),
  isVar, varTerm, occursVTerm, foldVarsVTerm, varsVTerm, viewTerm,
  isHomPair, isHomEnc, sortCompare, sortOfLTerm, sortGEQ,
  evalFreshAvoiding, freshLVar)
-- Lit(Var, Con), IsConst, isVar, varTerm, termVar, foldVarsVTerm, varsVTerm, occursVTerm come from Term.VTerm
-- isHomPair, isHomEnc come from Term.Term
-- TermView(Lit, FApp), viewTerm, termViewToTerm come from Term.Term.Raw

import Term.Rewriting.Definitions (Equal(..), eqsToType, Match, flattenMatch)
import Term.Substitution.SubstVFree (LSubst, substFromList, applyVTerm)
import Term.Substitution.SubstVFresh (LSubstVFresh, substFromListVFresh)

-- Matching Algorithm using the Unification Algorithm
-----------------------------------------------------

-- | matchHomLTerm
-- NOTE: Tamarin does allow matching pair(x0,x1) with pair(x1,x0) even though the substitution
-- x0 <~ x1, x1 <~ x0 is not allowed in unification.
-- NOTE: The variables orgVars are given to unifyHomLTermWithVars such that when 
-- creating new variables, unifyHomLTermWithVars can also take into account the 
-- variables that we turned into Consts in toMConstA.
-- NOTE: Id-substitutions (like x0 <~ x0) are being removed by the substFromList function.
matchHomLTerm :: IsConst c => (c -> LSort) -> Match (LTerm c) -> [LSubst c]
matchHomLTerm sortOf matchProblem = let
  ms = fromMaybe [] (flattenMatch matchProblem)
  eqs = map (\(t,p) -> Equal (toMConstA t) (toMConstC p)) ms
  orgVars = foldVarsVTerm $ foldr (\(t,p) vs -> t:p:vs) [] ms
  rangeVars = foldVarsVTerm $ map fst ms
  domainVars = foldVarsVTerm $ map snd ms
  sortOfConst = sortOfMConst sortOf
  in toMatcher $ cleanSubMatch domainVars rangeVars 
    =<< fromMConstSubst 
    =<< solvedFormOrdering sortOfConst
    =<< applyCapUnification sortOfConst (eqs, orgVars)
  where
    fromMConstSubst :: IsConst c1 => PreSubst (MConst c1) -> Maybe (PreSubst c1)
    fromMConstSubst = Just . first (map (second fromMConst))
    toMatcher :: IsConst c1 => Maybe (PreSubst c1) -> [LSubst c1]
    toMatcher pr = case pr of
      Nothing -> []
      Just s  -> [substFromList $ fst s]

-- Unification Algorithm Wrapper
--------------------------------

unifyHomLTerm :: IsConst c => (c -> LSort) -> [Equal (LTerm c)] -> [LSubstVFresh c]
unifyHomLTerm sortOf eqs = let
  orgVars = foldVarsVTerm $ eqsToType eqs
  in toUnifier $ cleanSubUnif orgVars 
    =<< toFreeAvoid orgVars 
    =<< solvedFormOrdering sortOf 
    =<< applyCapUnification sortOf (eqs, orgVars)
  where
    toUnifier :: IsConst c1 => Maybe (PreSubst c1) -> [LSubstVFresh c1]
    toUnifier pr = case pr of
      Nothing -> []
      Just s  -> [substFromListVFresh $ fst s]

-- Helper types
---------------

-- | Types to make it easier to have an overview of the algorithm 
-- NOTE: we chose not sets for diffrent reasons
-- Variables: 
-- - we want the number of occurences to matter in certain parts of the code
-- - efficiency of insertion
-- - additionally, we always use either foldVars or add new vars, which creates a duplicate free list
-- Equations:
-- - even using sets, {t1 = t2, t2 = t1} would still be valid sets. as such, insertion and
--   management will get even costlier. meanwhile the varsub rule takes care of duplicates
--   more elegantly. in general, we argue that as long as duplicates exist, there is always
--   a rule that is applicable. 
type PreSubst c = ([(LVar, LTerm c)], [LVar])
type EqsSubst a = ([Equal a], [LVar])

-- Helper function for types
combineAnySubst :: ([a], [b]) -> ([a], [b]) -> ([a], [b])
combineAnySubst (es1,vs1) (es2,vs2) = (es1++es2, vs1++vs2)

-- Type to translate HomorphicRuleReturn
data MaybeWFail a = MJust a | MNothing | MFail

-- Cap Unification Algorithm: Applying Homomorphic Rules
--------------------------------------------------------

-- | @unifyHomLNTerm eqs@ returns a set of unifiers for @eqs@ modulo EpsilonH.
-- returns a substitution for terms so that they unify or an empty list 
-- if it is not possible to unify the terms
-- Types used:
-- LNTerm = Term (Lit (Con Name | Var LVar) | FApp FunSym [Term Lit ((Con Name | Var LVar))])
-- use viewTerm to use "case of" term
-- Equal LNTerm = Equal { eqLHS :: LNTerm, eqRHS :: LNTerm }
-- sortOfName :: Name -> LSort
-- data LSort = LSortPub | LSortFresh | LSortMsg | LSortNode -- Nodes are for dependency graphs
applyCapUnification :: IsConst c => (c -> LSort) -> EqsSubst (LTerm c) -> Maybe (EqsSubst (LTerm c))
applyCapUnification sortOf eqsSubst = let
  lpeEqsSubst = first (map (fmap $ toLPETerm . normHom)) eqsSubst
  unifier = applyHomRules sortOf allHomRules lpeEqsSubst
  in Just . first (map (fmap lTerm)) =<< unifier

-- | Applies all homomorphic rules given en block, i.e., 
-- it applies the first rule always first after each change
-- Holds for output: No equation is a duplicate of another equation
applyHomRules :: IsConst c => (c -> LSort) -> [HomRule c] -> EqsSubst (LPETerm c) -> Maybe (EqsSubst (LPETerm c))
applyHomRules _ [] eqsSubst = Just eqsSubst -- no more rules to apply 
applyHomRules sortOf (rule:rules) eqsSubst =
  case applyHomRule sortOf rule eqsSubst [] of
    MJust newEqsSubst -> applyHomRules sortOf allHomRules newEqsSubst
    MNothing          -> applyHomRules sortOf rules eqsSubst
    MFail             -> Nothing

-- | Applies the homomorphic rule to the first term possible in equation list or returns Nothing 
-- if the rule is not applicable to any terms
applyHomRule :: IsConst c => (c -> LSort) -> HomRule c -> EqsSubst (LPETerm c) -> [Equal (LPETerm c)] -> MaybeWFail (EqsSubst (LPETerm c))
applyHomRule _ _ ([], _) _ = MNothing
applyHomRule sortOf rule (e:es, allVars) passedEqs = let eqsSubst = (es ++ passedEqs, allVars) in
  case rule e sortOf eqsSubst of
    HEqs            newSubst -> MJust $ combineAnySubst eqsSubst newSubst
    HSubstEqs subst newSubst -> MJust $ combineAnySubst (applyEqsSubst subst eqsSubst) newSubst
    HNothing                 -> applyHomRule sortOf rule (es, allVars) (e:passedEqs)
    HFail                    -> MFail
  where
    applyEqsSubst :: IsConst c1 => [(LVar, LTerm c1)] -> EqsSubst (LPETerm c1) -> EqsSubst (LPETerm c1)
    applyEqsSubst subst = first (map (fmap (toLPETerm . normHom . applyVTerm (substFromList subst) . lTerm)))

-- | To Homomorphic Solved Form (EqsSubst to PreSubst)
------------------------------------------------------

-- Returns a ordering in which each LVar in the tuple is unique or Nothing
-- This function also filters out all equations, for which the correpsonding substitution has a variable on the left side, 
-- that is not part of original Variables (Note that for matching, are only the variables in p), as otherwise, it was 
-- tested that the EquationStore will at some point have a substitution for which dom and vrange coincide in that variable.  
solvedFormOrdering :: IsConst c => (c -> LSort) -> EqsSubst (LTerm c) -> Maybe (PreSubst c)
solvedFormOrdering sortOf (eqs, allVars) = let
  substM = map (moveVarLeft sortOf) eqs
  (substDub, substNonDub) = partitionEithers $ catMaybes substM
  substNonDubVars = uncurry (++) $ second foldVarsVTerm $ unzip substNonDub
  duplicateVars = nub 
    $ (\xs -> [x | x <- xs, 1 < length (filter (== x) xs)]) 
    $ foldr (\(l,r) vars -> l:r:vars) substNonDubVars substDub
  substDubOrderedM = map (dubVarLeft duplicateVars) substDub
  substDubOrdered = map (second varTerm) $ catMaybes substDubOrderedM
  subst = substNonDub ++ substDubOrdered
  in if all isJust substM && all isJust substDubOrderedM && allLeftVarsUnique subst && allLeftVarsNotRight subst
    then Just (subst, allVars)
    else Nothing

moveVarLeft :: IsConst c => (c -> LSort) -> Equal (LTerm c) -> Maybe (Either (LVar, LVar) (LVar, LTerm c))
moveVarLeft sortOf (Equal l r) = case (viewTerm l, viewTerm r) of
  (Lit (Var lv), Lit (Var rv)) | lvarSort lv == lvarSort rv                           -> Just $ Left  (lv, rv) 
  (Lit (Var lv), Lit (Var rv)) | sortCompare (lvarSort lv) (lvarSort rv) == Just GT   -> Just $ Right (lv, r)
  (Lit (Var lv), Lit (Var rv)) | sortCompare (lvarSort lv) (lvarSort rv) == Just LT   -> Just $ Right (rv, l)
  (Lit (Var lv), Lit (Var rv)) | isNothing $ sortCompare (lvarSort lv) (lvarSort rv)  -> Nothing -- Uncomparable sorts should have been caught
  (Lit (Var lv), _           ) | sortGEQ sortOf lv r                      -> Just $ Right (lv, r)
  (_,            Lit (Var rv)) | sortGEQ sortOf rv l                      -> Just $ Right (rv, l)
  (_,_)                                                                               -> Nothing
  
-- We assume: if both variables are unique, even in matching, the order does not play a role
dubVarLeft :: [LVar] -> (LVar, LVar) -> Maybe (LVar, LVar)
dubVarLeft otherVars (l,r) = case (l `notElem` otherVars, r `notElem` otherVars) of
  (True,  True)  -> Just (l,r) 
  (True,  False) -> Just (l,r)
  (False, True)  -> Just (r,l)
  (False, False) -> Nothing

allLeftVarsUnique :: [(LVar, a)] -> Bool
allLeftVarsUnique [] = True
allLeftVarsUnique ((vL,_):substs) = not (any (\(vR,_) -> vL == vR) substs) && allLeftVarsUnique substs

allLeftVarsNotRight :: [(LVar, LTerm c)] -> Bool
allLeftVarsNotRight subst = let (vars,terms) = unzip subst in not $ any (\v -> v `elem` foldVarsVTerm terms) vars

-- To Free Avoid
----------------

toFreeAvoid :: IsConst c => [LVar] -> PreSubst c -> Maybe (PreSubst c)
toFreeAvoid orgVars subst = let
  freeAvoidingSubst = getFreeAvoidingSubstOfTerms orgVars ([], snd subst) (map snd (fst subst))
  completeSubst = combineAnySubst freeAvoidingSubst (applyPreSubstToVrange freeAvoidingSubst subst)
  in Just completeSubst
  where
    applyPreSubstToVrange :: IsConst c1 => PreSubst c1 -> PreSubst c1 -> PreSubst c1
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
      else let newV = evalFreshAvoiding (freshLVar (lvarName x) (lvarSort x)) allVs in 
        ((x, varTerm newV):newSubst, newV:allVs)
    (FApp _ args) -> getFreeAvoidingSubstOfTerms orgVars (newSubst, allVs) args


-- Clean up Substitution
------------------------

cleanSubMatch :: IsConst c => [LVar] -> [LVar] -> PreSubst c -> Maybe (PreSubst c)
cleanSubMatch orgVars rangeVars (subst, allVs) = let
  cleanSubst1 = filter ((`elem` orgVars) . fst) subst
  cleanSubst2 = filter (all (`elem` rangeVars) . varsVTerm . snd) cleanSubst1
  in Just (cleanSubst2, allVs)

cleanSubUnif :: IsConst c => [LVar] -> PreSubst c -> Maybe (PreSubst c)
cleanSubUnif orgVars (subst, allVs) = let
  cleanSubst = filter ((`elem` orgVars) . fst) subst
  in Just (cleanSubst, allVs)

-- Homomorphic Rules Managers
-----------------------------

-- | Return type for a HomRule
data HomRuleReturn c =
    HEqs                        (EqsSubst (LPETerm c))
  | HSubstEqs [(LVar, LTerm c)] (EqsSubst (LPETerm c))
  | HNothing
  | HFail
  deriving (Show, Eq)

-- | Type for rules applied to equations for unification modulo EpsilonH
-- @arg1 = equation which we try to apply the rule on
-- @arg2 = translation from terms to sorts
-- @arg3 = all other equations (may be needed to check if a variable occurs in them)
type HomRule c = Equal (LPETerm c) -> (c -> LSort) -> EqsSubst (LPETerm c) -> HomRuleReturn c

-- | All homomorphic rules in order of application
-- All rules are added as such that they are first applied on the equation
-- Equal (eqLHS eq) (eqRHS eq) and then on the equation Equal (eqRHS eq) (eqLHS eq)
-- with eq being the first argument given to the function
allHomRules :: IsConst c => [HomRule c]
allHomRules = map (\r -> combineWrapperHomRule r (switchedWrapperHomRule r))
  -- failure rules first
  [ failureOneHomRule
  , failureTwoHomRule
  , occurCheckHomRule
  , clashHomRule
  -- new failure rules
  , differentConsts
  , doSortsCompare
  -- then homomorphic patterns   
  -- shaping best before parsing  
  , shapingHomRule
  , parsingHomRule
  -- varSub en block with homorphic patterns
  , variableSubstitutionHomRule
  -- then other rules
  , trivialHomRule
  , stdDecompositionHomRule ]

-- | Combines two rules and runs the second rule if first returns HNothing
combineWrapperHomRule :: IsConst c => HomRule c -> HomRule c -> HomRule c
combineWrapperHomRule rule1 rule2 eq sortOf eqsSubst =
  case rule1 eq sortOf eqsSubst of
    HNothing -> rule2 eq sortOf eqsSubst
    ret      -> ret

-- | Since the equality sign used is not oriented, we need
-- to look at the possibility of rule applications for 
-- both x = t and t = x for any equation.
-- This function is used in combination with combineWrapperHomRule
switchedWrapperHomRule :: IsConst c => HomRule c -> HomRule c
switchedWrapperHomRule rule eq = rule (Equal (eqRHS eq) (eqLHS eq))

-- | used to export homomorphic rules for debugging
debugHomRule :: IsConst c => Int -> HomRule c
debugHomRule i = allHomRules !! i

-- | Standard syntactic inference rules
-----------------------------------------

trivialHomRule :: IsConst c => HomRule c
trivialHomRule (Equal eL eR) _ _ = if lTerm eL == lTerm eR then HEqs ([], []) else HNothing

stdDecompositionHomRule :: IsConst c => HomRule c
stdDecompositionHomRule (Equal eL eR) _ _ =
  case (viewTermPE eL, viewTermPE eR) of
    (FApp lfsym largs, FApp rfsym rargs) | lfsym == rfsym && length largs == length rargs
      -> HEqs (zipWith (\l r -> Equal (toLPETerm l) (toLPETerm r)) largs rargs, [])
    _ -> HNothing

variableSubstitutionHomRule :: IsConst c => HomRule c
variableSubstitutionHomRule (Equal eL eR) sortOf (eqs,_) = let tR = lTerm eR in
  case (viewTermPE eL, viewTermPE eR) of
    (Lit (Var vl), Lit (Var vr)) | lvarSort vl == lvarSort vr ->
      if vl /= vr && occursVTermEqs vl eqs && occursVTermEqs vr eqs
      then HSubstEqs [(vl, tR)] ([Equal eL eR], [])
      else HNothing
    (Lit (Var vl), _) ->
      if not (occursVTerm vl tR) && occursVTermEqs vl eqs && sortGEQ sortOf vl tR
      then HSubstEqs [(vl, tR)] ([Equal eL eR], [])
      else HNothing
    _ -> HNothing
    where
      occursVTermEqs :: LVar -> [Equal (LPETerm c)] -> Bool
      occursVTermEqs v es = any (occursVTerm v . lTerm) (eqsToType es)

clashHomRule :: IsConst c => HomRule c
clashHomRule (Equal eL eR) _ _ = let tL = lTerm eL; tR = lTerm eR
  in case (viewTermPE eL, viewTermPE eR) of
    (FApp lfsym _, FApp rfsym _) | lfsym /= rfsym && not (isHomPair tL && isHomEnc tR) && not (isHomEnc tL && isHomPair tR)
      -> HFail
    _ -> HNothing

occurCheckHomRule :: IsConst c => HomRule c
occurCheckHomRule (Equal tL tR) _ _ = case viewTermPE tL of
    (Lit (Var vL)) | tL /= tR && occursVTerm vL (lTerm tR) -> HFail
    _                                                      -> HNothing

-- | Newly added rules for incompatible sorts
---------------------------------------------

-- Checks if consts can be unified
differentConsts :: IsConst c => HomRule c
differentConsts (Equal eL eR) _ _ = case (viewTermPE eL, viewTermPE eR) of
  (Lit (Con cl), Lit (Con cr)) -> if cl == cr then HNothing else HFail
  (Lit (Con _ ), Lit (Var _ )) -> HNothing
  (Lit (Con _ ), _           ) -> HFail
  (Lit (Var _ ), Lit (Con _ )) -> HNothing
  (_,            Lit (Con _ )) -> HFail
  _                            -> HNothing

-- Checks if sorts are incompatible
doSortsCompare :: IsConst c => HomRule c
doSortsCompare (Equal eL eR) sortOf _ = case (viewTermPE eL, viewTermPE eR) of
  (Lit (Var vl), Lit (Var vr)) ->
    if sortGEQ sortOf vl (lTerm eR) || sortGEQ sortOf vr (lTerm eL) then HNothing else HFail
  (Lit (Var vl), _           ) ->
    if sortGEQ sortOf vl (lTerm eR) then HNothing else HFail
  (_,            Lit (Var vr)) ->
    if sortGEQ sortOf vr (lTerm eL) then HNothing else HFail
  _                            ->
    if isJust $ sortCompare (sortOfLTerm sortOf $ lTerm eL) (sortOfLTerm sortOf $ lTerm eR) then HNothing else HFail

-- | Homomorphic Patterns
-------------------------

shapingHomRule :: IsConst c => HomRule c
shapingHomRule (Equal eL eR) _ (_, allVars) = let
  eRepsLHS = eRepsTerms $ pRep eL
  n = length (eRep eR) - 1
  in if length eRepsLHS > 1 && n >= 1
  then case findQualifyingETerm eRepsLHS n 0 of
    Just (qualifyingIndex, qualifyingELhs, x) -> let
      m = n + 2 - length qualifyingELhs
      xFresh = evalFreshAvoiding (freshLVar "sh" LSortMsg) allVars
      lhs1NewPTerm = let (ys,zs) = splitAt qualifyingIndex eRepsLHS in
        PRep (eRepsString $ pRep eL)
        (ys ++ [[varTerm xFresh] ++ take (m-1) (tail (eRep eR)) ++ tail qualifyingELhs] ++ tail zs)
      lhs1 = toLPETerm $ normHom $ fromPRepresentation lhs1NewPTerm
      rhs2 = toLPETerm $ normHom $ fromERepresentation $ varTerm xFresh : take (m-1) (tail (eRep eR))
      in HEqs ([Equal lhs1 eR, Equal (toLPETerm $ varTerm x) rhs2], [xFresh])
    Nothing -> HNothing
  else HNothing
  where
    findQualifyingETerm :: IsConst c1 => [ERepresentation c1] -> Int -> Int -> Maybe (Int, ERepresentation c1, LVar)
    findQualifyingETerm [] _ _ = Nothing
    findQualifyingETerm (e:es) n ind = case viewTerm (head e) of
      (Lit (Var v)) | (length e - 1 < n) && not (null e) -> Just (ind, e, v)
      _                                                  -> findQualifyingETerm es n (ind+1)

failureOneHomRule :: IsConst c => HomRule c
failureOneHomRule (Equal eL eR) _ _ = let
    (tL, tR) = (lTerm eL, lTerm eR)
    tLNonKey = filter (\(p,_) -> all ('1' ==) (ePosition p tL)) (positionsWithTerms tL)
    tRNonKey = filter (\(p,_) -> all ('1' ==) (ePosition p tR)) (positionsWithTerms tR)
  in if any (\(mL,mR) -> positionsIncompatible mL tL mR tR) (matchVars tLNonKey tRNonKey)
  then HFail
  else HNothing
  where
    matchVars :: IsConst c1 => [(String, LTerm c1)] -> [(String, LTerm c1)] -> [(String, String)]
    matchVars [] _ = []
    matchVars (v:vs) vs2 =
      let matches = filter (\vv2 -> snd v == snd vv2) vs2 in
      if isVar (snd v) && not (null matches)
      then map (\(m,_) -> (fst v, m)) matches ++ matchVars vs vs2
      else matchVars vs vs2

failureTwoHomRule :: IsConst c => HomRule c
failureTwoHomRule (Equal eL eR) _ _ = let eRepsLHS = eRepsTerms $ pRep eL in
  if any (\e -> not (isVar $ head e) && (length e < length (eRep eR))) eRepsLHS && length eRepsLHS > 1
  then HFail
  else HNothing

-- check both directions
-- check any other thingens
-- add other checks also here (like pair and henc but not other different)
-- give better name
fastTestUnifiableHom :: IsConst c => LTerm c -> LTerm c -> Bool
fastTestUnifiableHom l r = let
    lPE = toLPETerm $ normHom l
    rPE = toLPETerm $ normHom r
    returns =  [
      failureOneHomRule (Equal lPE rPE) (const LSortMsg) ([], []),
      failureOneHomRule (Equal rPE lPE) (const LSortMsg) ([], []),
      failureTwoHomRule (Equal lPE rPE) (const LSortMsg) ([], []),
      failureTwoHomRule (Equal rPE lPE) (const LSortMsg) ([], []),
      occurCheckHomRule (Equal lPE rPE) (const LSortMsg) ([], []),
      occurCheckHomRule (Equal rPE lPE) (const LSortMsg) ([], []),
      clashHomRule (Equal lPE rPE) (const LSortMsg) ([], []),
      clashHomRule (Equal rPE lPE) (const LSortMsg) ([], []),
      differentConsts (Equal lPE rPE) (const LSortMsg) ([], []),
      differentConsts (Equal rPE lPE) (const LSortMsg) ([], [])
      -- can't check doSortsCompare since this function should be callable without 
      -- sort information on the terms
      ]
    in all (== HNothing) returns
    
parsingHomRule :: IsConst c => HomRule c
parsingHomRule (Equal eL eR) _ _ = let
  eRepsLHS = eRepsTerms $ pRep eL
  newLHS = toLPETerm $ normHom $ fromPRepresentation $ PRep (eRepsString $ pRep eL) (map init eRepsLHS)
  newRHS = toLPETerm $ normHom $ fromERepresentation $ init (eRep eR)
  allKms = map (toLPETerm . normHom) $ last (eRep eR) : map last eRepsLHS
  in if all (\t -> length t >= 2) (eRepsLHS ++ [eRep eR])
  then HEqs (Equal newLHS newRHS : getAllCombinations allKms, [])
  else HNothing
  where
    getAllCombinations :: IsConst c1 => [LPETerm c1] -> [Equal (LPETerm c1)]
    getAllCombinations [] = []
    getAllCombinations (x:xs) = map (Equal x) xs ++ getAllCombinations xs