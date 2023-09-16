{-# LANGUAGE LambdaCase #-}

module Term.Homomorphism.Unification (
  -- * Unification modulo EpsilonH for Homomorphic Encryption
    unifyHomomorphicLTerm

  -- * Matching modulo EpsilonH for Homomorphic Encryption
  , matchHomomorphicLTerm

  -- * For debugging
  , allLeftVarsNotRight
  , debugHomomorphicRule
  , HomomorphicRuleReturn(..)
) where

import Data.Maybe     (isJust, isNothing, mapMaybe, fromMaybe)
import Data.Bifunctor (bimap, first, second)

import Term.Homomorphism.LPETerm
import Term.Homomorphism.MConst

import Term.LTerm (
  LTerm, Lit(Var, Con), IsConst, LVar(..), TermView(FApp, Lit), LSort(..),
  termVar, isVar, varTerm, termVar, occursVTerm, varsVTerm, viewTerm,
  isPair, isHomEnc, sortCompare, sortOfLTerm)
-- Lit(Var, Con), IsConst, isVar, varTerm, termVar, varsVTerm, occursVTerm come from Term.VTerm
-- isPair, isHomEnc come from Term.Term
-- TermView(Lit, FApp), viewTerm, termViewToTerm come from Term.Term.Raw

import Term.Rewriting.Definitions (Equal(..))
import Term.Substitution.SubstVFree (LSubst, substFromList, applyVTerm)
import Term.Substitution.SubstVFresh (LSubstVFresh, substFromListVFresh)

import Extension.Prelude (sortednub)

-- Matching Algorithm using the Unification Algorithm
-----------------------------------------------------

-- | matchHomomorphicLTerm
-- orgVars are given to unifyHomomorphicLTermWithVars such that when creating new variables, unifyHomomorphicLTermWithVars can
-- also take into account the variables that we turned into Consts in toMConstA.
matchHomomorphicLTerm :: IsConst c => (c -> LSort) -> [(LTerm c, LTerm c)] -> Maybe (LSubst c)
matchHomomorphicLTerm sortOf ms = let
  sO = sortOfMConst sortOf
  eqs = map (\(t,p) -> Equal (toMConstA t) (toMConstC p)) ms
  orgVars = foldVars $ foldr (\(t,p) vs -> t:p:vs) [] ms
  orgLVars = foldVars $ map snd ms
  unifier = unifyHomomorphicLTermWithVars sO (eqs, orgVars)
  in toSingleSubst orgLVars =<< checkMatchSubst ms =<< cleanupSubst =<< substFromMConst =<< toSubstForm sO orgLVars =<< unifier

-- Unification Algorithm Wrapper
--------------------------------

unifyHomomorphicLTerm :: IsConst c => (c -> LSort) -> [Equal (LTerm c)] -> Maybe (LSubst c, LSubstVFresh c)
unifyHomomorphicLTerm sortOf eqs = let
  orgVars = foldVars $ eqsToTerms eqs
  unifier = unifyHomomorphicLTermWithVars sortOf (eqs, orgVars)
  in toDoubleSubst orgVars =<< toFreeAvoid orgVars =<< toSubstForm sortOf orgVars =<< unifier

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
    applyEqsSubst subst = first (map (fmap (toLPETerm . applyVTerm (substFromList subst) . lTerm)))

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
  in if not (any isMFail substWODubVars) && isJust substM
  then checkSubst orgVars (subst, allVars)
  else Nothing

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
  in checkFreeAvoidSubst orgVars subst =<< checkSubst orgVars completeSubst
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

toDoubleSubst :: [LVar] -> PreSubst c -> Maybe (LSubst c, LSubstVFresh c)
toDoubleSubst orgVars subst = Just . (\s -> (substFromList s, substFromListVFresh s)) . fst =<< checkSubst orgVars subst

toSingleSubst :: [LVar] -> PreSubst c -> Maybe (LSubst c)
toSingleSubst orgVars subst = Just . substFromList . fst =<< checkSubst orgVars subst

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
  -- new failure rule
  , differentConsts
  , doSortsCompare
  -- homomorphic normalizin rule
  -- then Homomorphic patterns   
  -- shaping best before parsing  
  , shapingHomomorphicRule
  , parsingHomomorphicRule
  -- varSub en block with Homorphic patterns
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
trivialHomomorphicRule (Equal el er) _ _ = if lTerm el == lTerm er then HEqs ([],[]) else HNothing

stdDecompositionHomomorphicRule :: IsConst c => HomomorphicRule c
stdDecompositionHomomorphicRule (Equal el er) _ _ =
  case (viewTermPE el, viewTermPE er) of
    (FApp lfsym largs, FApp rfsym rargs) ->
      if lfsym == rfsym && length largs == length rargs
      then HEqs (zipWith (\l r -> Equal (toLPETerm l) (toLPETerm r)) largs rargs, [])
      else HNothing
    (_,_) -> HNothing

variableSubstitutionHomomorphicRule :: IsConst c => HomomorphicRule c
variableSubstitutionHomomorphicRule eq sortOf (eqs,_) = let eR = lTerm $ eqRHS eq in
  case (viewTermPE $ eqLHS eq, viewTermPE $ eqRHS eq) of
    (Lit (Var vl), Lit (Var vr)) | lvarSort vl == lvarSort vr ->
      if vl /= vr && occursVTermEqs vl eqs && occursVTermEqs vr eqs
      then HSubstEqs [(vl, eR)] ([eq],[])
      else HNothing
    (Lit (Var vl), _) ->
      if not (occursVTerm vl eR) && occursVTermEqs vl eqs && sortCorrectForSubst sortOf vl eR
      then HSubstEqs [(vl, eR)] ([eq],[])
      else HNothing
    _ -> HNothing

clashHomomorphicRule :: IsConst c => HomomorphicRule c
clashHomomorphicRule eq _ _ = let
    tL = lTerm $ eqLHS eq
    tR = lTerm $ eqRHS eq
  in case (viewTerm tL, viewTerm tR) of
    (FApp lfsym _, FApp rfsym _) ->
      if lfsym == rfsym || (isPair tL && isHomEnc tR) || (isHomEnc tL && isPair tR)
      then HNothing
      else HFail
    (_,_) -> HNothing

occurCheckHomomorphicRule :: IsConst c => HomomorphicRule c
occurCheckHomomorphicRule eq _ _ =
  case termVar $ lTerm $ eqLHS eq of
    Just v  -> if
        (lTerm (eqLHS eq) /= lTerm (eqRHS eq))
        && occursVTerm v (lTerm $ eqRHS eq)
      then HFail
      else HNothing
    Nothing -> HNothing

-- | Newly added rules for incompatible sorts
---------------------------------------------

-- Checks if consts can be unified
differentConsts :: IsConst c => HomomorphicRule c
differentConsts (Equal el er) _ _ = case (viewTermPE el, viewTermPE er) of
  (Lit (Con cl), Lit (Con cr)) -> if cl == cr then HNothing else HFail
  (Lit (Con _ ), Lit (Var _ )) -> HNothing
  (Lit (Con _ ), _           ) -> HFail
  (Lit (Var _ ), Lit (Con _ )) -> HNothing
  (_,            Lit (Con _ )) -> HFail
  _                            -> HNothing

-- Checks if sorts are incompatible
doSortsCompare :: IsConst c => HomomorphicRule c
doSortsCompare (Equal el er) sortOf _ = case (viewTermPE el, viewTermPE er) of
  (Lit (Var vl), Lit (Var vr)) -> if sortCorrectForSubst sortOf vl (lTerm er) || sortCorrectForSubst sortOf vr (lTerm el) then HNothing else HFail
  (Lit (Var vl), _           ) -> if sortCorrectForSubst sortOf vl (lTerm er) then HNothing else HFail
  (_,            Lit (Var vr)) -> if sortCorrectForSubst sortOf vr (lTerm el) then HNothing else HFail
  _                            -> if isJust $ sortCompare (sortOfLTerm sortOf $ lTerm el) (sortOfLTerm sortOf $ lTerm er) then HNothing else HFail

-- | Homomorphic Patterns
-------------------------

shapingHomomorphicRule :: IsConst c => HomomorphicRule c
shapingHomomorphicRule eq _ (_,allVars) = let
  eRepsLHS = eRepsTerms $ pRep $ eqLHS eq
  strsLHS = eRepsString $ pRep $ eqLHS eq
  eRepRHS = eRep $ eqRHS eq
  n = length eRepRHS - 1
  in if length eRepsLHS > 1 && n >= 1
  then case findQualifyingETerm eRepsLHS n 0 of
    Just qualifyingIndex -> let
      qualifyingELhs = eRepsLHS !! qualifyingIndex
      m = n + 2 - length qualifyingELhs
      x = head qualifyingELhs
      xFresh = getNewSimilarVar (LVar "sh" LSortMsg 0) allVars
      lhs1NewETerm = ([varTerm xFresh] ++ take (m-1) (tail eRepRHS) ++ tail qualifyingELhs)
      lhs1NewPTerm = let (ys,zs) = splitAt qualifyingIndex eRepsLHS in
        PRep strsLHS (ys ++ [lhs1NewETerm] ++ tail zs)
      lhs1 = toLPETerm $ fromPRepresentation lhs1NewPTerm
      rhs2 = toLPETerm $ fromERepresentation $ varTerm xFresh : take (m-1) (tail eRepRHS)
      in HEqs ([Equal lhs1 (eqRHS eq), Equal (toLPETerm x) rhs2], [xFresh])
    Nothing -> HNothing
  else HNothing
  where
    findQualifyingETerm :: IsConst c => [ERepresentation c] -> Int -> Int -> Maybe Int
    findQualifyingETerm [] _ _ = Nothing
    findQualifyingETerm (e:es) n ind =
      if (length e - 1 < n) && not (null e) && isVar (head e)
      then Just ind
      else findQualifyingETerm es n (ind+1)

failureOneHomomorphicRule :: IsConst c => HomomorphicRule c
failureOneHomomorphicRule eq _ _ = let
    t1 = lTerm $ eqLHS eq
    t2 = lTerm $ eqRHS eq
    t1Pos = positionsWithTerms t1
    t2Pos = positionsWithTerms t2
    t1NonKey = filter (\(p,_) -> all ('1' ==) (ePosition p t1)) t1Pos
    t2NonKey = filter (\(p,_) -> all ('1' ==) (ePosition p t2)) t2Pos
    matchedVars = matchVars t1NonKey t2NonKey
  in if (t1 /= t2) && any (\(m1,m2) -> positionsIncompatible m1 t1 m2 t2) matchedVars
  then HFail
  else HNothing
  where
    matchVars :: IsConst c => [(String, LTerm c)] -> [(String, LTerm c)] -> [(String, String)]
    matchVars [] _ = []
    matchVars _ [] = []
    matchVars (v:vs) vs2 =
      let matches = filter (\vv2 -> snd v == snd vv2) vs2 in
      if isVar (snd v) && not (null matches)
      then map (\(m,_) -> (fst v, m)) matches ++ matchVars vs vs2
      else matchVars vs vs2

failureTwoHomomorphicRule :: IsConst c => HomomorphicRule c
failureTwoHomomorphicRule eq _ _ = let
  n = length (eRep $ eqRHS eq) - 1
  eRepsLHS = eRepsTerms $ pRep $ eqLHS eq
  in if any (\e -> not (isVar $ head e) && (length e < n + 1)) eRepsLHS && length eRepsLHS > 1 
  then HFail
  else HNothing

parsingHomomorphicRule :: IsConst c => HomomorphicRule c
parsingHomomorphicRule eq _ _ = let
  eRepsLHS = eRepsTerms $ pRep $ eqLHS eq
  strRepsLHS = eRepsString $ pRep $ eqLHS eq
  newERepsLHS = map init eRepsLHS
  eRepRHS = eRep $ eqRHS eq
  newLHS = toLPETerm $ fromPRepresentation $ PRep strRepsLHS newERepsLHS
  newRHS = toLPETerm $ fromERepresentation $ init eRepRHS
  allKms = map toLPETerm $ last eRepRHS : map last eRepsLHS
  in if all (\t -> length t >= 2) (eRepsLHS ++ [eRepRHS])
  then HEqs (Equal newLHS newRHS : getAllCombinations allKms, [])
  else HNothing
  where
    getAllCombinations :: IsConst c => [LPETerm c] -> [Equal (LPETerm c)]
    getAllCombinations [] = []
    getAllCombinations (x:xs) = pairCombinations x xs ++ getAllCombinations xs
    pairCombinations _ [] = []
    pairCombinations x (y:ys) = Equal x y : pairCombinations x ys

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
getNewSimilarVar x allVars = LVar (lvarName x) (lvarSort x) $ (+) 1 $ foldr (max . lvarIdx) (lvarIdx x) (filter (\e -> lvarName x == lvarName e) allVars)

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

-- | Sanity checks
------------------

cleanupSubst :: IsConst c => PreSubst c -> Maybe (PreSubst c)
cleanupSubst subst = let cleanSubst = first (removeDuplicates . removeEqsToSelf) subst in
  if isCorrectSubst cleanSubst then Just cleanSubst else Nothing

removeEqsToSelf :: IsConst c => [(LVar, LTerm c)] -> [(LVar, LTerm c)]
removeEqsToSelf = filter (\(v,t) -> varTerm v /= t)

removeDuplicates :: IsConst c => [(LVar, LTerm c)] -> [(LVar, LTerm c)]
removeDuplicates [] = []
removeDuplicates ((v1,t1):es) =
  if any (\(v2,t2) -> (v1 == v2 && t1 == t2) || (varTerm v1 == t2 && t1 == varTerm v2)) es
  then removeDuplicates es
  else (v1,t1) : removeDuplicates es

isCorrectSubst :: PreSubst c -> Bool
isCorrectSubst (s,_) = allLeftVarsUnique s && allLeftVarsNotRight s

checkSubst :: [LVar] -> PreSubst c -> Maybe (PreSubst c)
checkSubst orgVars (s,v) =
  if allLeftVarsUnique s && allLeftVarsNotRight s && all ((`elem` orgVars) . fst) s 
  then Just (s,v) else Nothing

checkMatchSubst :: [(LTerm c, LTerm c)] -> PreSubst c -> Maybe (PreSubst c)
checkMatchSubst ms subst = let
  (tVars, pVars) = bimap foldVars foldVars $ unzip ms
  (leftVars, rightVars) = second foldVars $ unzip $ fst subst
  in if all (\v -> v `notElem` leftVars  || v `elem` pVars) tVars
     && all (\v -> v `notElem` rightVars || v `elem` tVars) pVars
     && all (`elem` pVars) leftVars && all (`elem` tVars) rightVars
  then Just subst else Nothing

checkFreeAvoidSubst :: [LVar] -> PreSubst c -> PreSubst c -> Maybe (PreSubst c)
checkFreeAvoidSubst orgVars orgSubst completeSubst = let
  (cmpLVars, cmpRVars) = second foldVars $ unzip $ fst completeSubst
  (_, orgRVars) = second foldVars $ unzip $ fst orgSubst
  in if all (`notElem` cmpRVars) orgVars
     && all (\v -> v `notElem` orgVars || v `elem` cmpLVars) orgRVars
  then Just completeSubst else Nothing

allLeftVarsUnique :: [(LVar, a)] -> Bool
allLeftVarsUnique [] = True
allLeftVarsUnique ((v1,_):substs) = not (any (\(v2,_) -> v1 == v2) substs) && allLeftVarsUnique substs

allLeftVarsNotRight :: [(LVar, LTerm c)] -> Bool
allLeftVarsNotRight subst = let (vars,terms) = unzip subst in not $ any (\v -> v `elem` foldVars terms) vars