{-# LANGUAGE DeriveDataTypeable #-}

module Term.Homomorphism.Unification (
  -- * Unification modulo EpsilonH for Homomorphic Encryption
    unifyHomomorphicLTerm

  -- * Matching modulo EpsilonH for Homomorphic Encryption
  , matchHomomorphicLTerm

  -- * For debugging
  , debugHomomorphicRule
  , HomomorphicRuleReturn(..)
) where

import Data.Map (fromList)
import Data.Maybe (fromMaybe, isJust, isNothing, catMaybes)
import Data.Bifunctor (second)

-- For data MConst
import Data.Typeable ( Typeable )
import Data.Data ( Data )

import Term.Homomorphism.LPETerm

import Term.LTerm (
  LTerm, Lit(Var, Con), IsConst, LVar(..), TermView(FApp, Lit), LSort(..),
  termVar, isVar, varTerm, termVar, occursVTerm, varsVTerm, viewTerm, termViewToTerm,
  isPair, isHomEnc, sortCompare, sortOfLTerm)
-- Lit(Var, Con), IsConst, isVar, varTerm, termVar, varsVTerm, occursVTerm come from Term.VTerm
-- isPair, isHomEnc come from Term.Term
-- TermView(Lit, FApp), viewTerm, termViewToTerm come from Term.Term.Raw

import Term.Rewriting.Definitions (Equal(..))
import Term.Substitution.SubstVFree (LSubst, Subst(..), substFromList, substToList, emptySubst, applyVTerm)
import Term.Substitution.SubstVFresh (LSubstVFresh, substFromListVFresh, emptySubstVFresh)

import Extension.Prelude (sortednub)

-- Matching Algorithm using the Unification Algorithm
-----------------------------------------------------

-- | matchHomomorphicLTerm
-- TODO: need to solve the case where we transform consts back to vars and suddenly the substitution has same vars in both dom and vrange
-- Due to the switching from vars to constants we need to store the vars seperately as to not create a new var that already exists TODO: describe better
matchHomomorphicLTerm :: IsConst c => (c -> LSort) -> [(LTerm c, LTerm c)] -> Maybe (Subst c LVar)
matchHomomorphicLTerm sortOf ms = let
    eqs = map (\(t,p) -> Equal (toMConstA t) (toMConstC p)) ms
  in case unifyHomomorphicLTermWithVars (sortOfMConst sortOf) (foldVars $ eqsToTerms eqs) of
    Just (s,_) -> Just $ substFromList $ removeSubstsToSelf $ map (second fromMConst) $ substToList s
    Nothing    -> if all (uncurry (==)) ms then Just emptySubst else Nothing

-- TODO: make full sanity check instead of just removeSubstsToSelf
removeSubstsToSelf :: IsConst c => [(LVar, LTerm c)] -> [(LVar, LTerm c)]
removeSubstsToSelf = filter (\(v,t) -> case viewTerm t of (Lit (Var vt)) | v == vt -> False; _ -> True)

-- Const type used by matching algorithm
data MConst c = MCon c | MVar LVar
  deriving (Eq, Ord, Show, Data, Typeable)

instance (Ord c, Eq c, Show c, Data c, IsConst c) => IsConst (MConst c) where

toMConstA :: IsConst c => LTerm c -> LTerm (MConst c)
toMConstA t = case viewTerm t of
  (FApp funsym args) -> termViewToTerm (FApp funsym $ map toMConstA args)
  (Lit (Var v))      -> termViewToTerm (Lit (Con (MVar v)))
  (Lit (Con c))      -> termViewToTerm (Lit (Con (MCon c)))

toMConstC :: IsConst c => LTerm c -> LTerm (MConst c)
toMConstC t = case viewTerm t of
  (FApp funsym args) -> termViewToTerm (FApp funsym $ map toMConstC args)
  (Lit (Var v))      -> termViewToTerm (Lit (Var v))
  (Lit (Con c))      -> termViewToTerm (Lit (Con (MCon c)))

fromMConst :: IsConst c => LTerm (MConst c) -> LTerm c
fromMConst t = case viewTerm t of
  (FApp funsym args)   -> termViewToTerm (FApp funsym $ map fromMConst args)
  (Lit (Var v))        -> termViewToTerm (Lit (Var v))
  (Lit (Con (MCon c))) -> termViewToTerm (Lit (Con c))
  (Lit (Con (MVar v))) -> termViewToTerm (Lit (Var v))

 -- con of nodes are messages somehow
sortOfMConst :: IsConst c => (c -> LSort) -> MConst c -> LSort
sortOfMConst sortOf (MCon c) = sortOf c
sortOfMConst _      (MVar v) = lvarSort v

-- Unification Algorithm using the Homomorphic Rules
----------------------------------------------------

unifyHomomorphicLTerm :: IsConst c => (c -> LSort) -> [Equal (LTerm c)] -> Maybe (LSubst c, LSubstVFresh c)
unifyHomomorphicLTerm sortOf eqs = unifyHomomorphicLTermWithVars sortOf (foldVars $ eqsToTerms eqs) eqs

-- | @unifyHomomorphicLNTerm eqs@ returns a set of unifiers for @eqs@ modulo EpsilonH.
-- returns a substitution for terms so that they unify or an empty list 
-- if it is not possible to unify the terms
-- Types used:
-- LNTerm = Term (Lit (Con Name | Var LVar) | FApp FunSym [Term Lit ((Con Name | Var LVar))])
-- use viewTerm to use "case of" term
-- Equal LNTerm = Equal { eqLHS :: LNTerm, eqRHS :: LNTerm }
-- sortOfName :: Name -> LSort
-- data LSort = LSortPub | LSortFresh | LSortMsg | LSortNode -- Nodes are for dependency graphs
-- TODO: can be written more elegantly
unifyHomomorphicLTermWithVars :: IsConst c => (c -> LSort) -> [LVar] -> [Equal (LTerm c)] -> Maybe (LSubst c, LSubstVFresh c)
unifyHomomorphicLTermWithVars sortOf allVars eqs =
  toSubst $ map (fmap lTerm) $ applyHomomorphicRules sortOf allVars allHomomorphicRules (map (fmap toLPETerm) eqsN)
  where
    eqsN = map (fmap normHomomorphic) eqs
    toSubst [] = if all (\eq -> eqLHS eq == eqRHS eq) eqsN then Just (emptySubst, emptySubstVFresh) else Nothing
    toSubst eqsSubst = case toHomomorphicSolvedForm sortOf eqsSubst of
      Just subst -> Just (substFromList subst, substFromListVFresh subst)
      Nothing -> Nothing

-- | Applies all homomorphic rules given en block, i.e., 
-- it applies the first rule always first after each change
applyHomomorphicRules :: IsConst c => (c -> LSort) -> [LVar] -> [HomomorphicRule c] -> [Equal (LPETerm c)] -> [Equal (LPETerm c)]
applyHomomorphicRules _ _ [] eqs = eqs -- no more rules to apply 
applyHomomorphicRules sortOf allVars (rule:rules) eqs =
  case applyHomomorphicRule sortOf allVars rule eqs [] of
    Just (newEqs, newVars) -> applyHomomorphicRules sortOf newVars allHomomorphicRules newEqs
    Nothing                -> applyHomomorphicRules sortOf allVars rules eqs

-- | Applies the homomorphic rule to the first term possible in equation list or returns Nothing 
-- if the rule is not applicable to any terms
applyHomomorphicRule :: IsConst c => (c -> LSort) -> [LVar] -> HomomorphicRule c -> [Equal (LPETerm c)] -> [Equal (LPETerm c)] -> Maybe ([Equal (LPETerm c)], [LVar])
applyHomomorphicRule _ _ _ [] _ = Nothing
applyHomomorphicRule sortOf allVars rule (equation:equations) passedEqs =
  case rule equation sortOf allVars (passedEqs ++ equations) of
    HEqs            newEqs newVars -> Just (passedEqs ++ newEqs ++ equations, allVars ++ newVars)
    HSubstEqs subst newEqs newVars -> Just (map (applySubstitution subst) (passedEqs ++ equations) ++ newEqs, allVars ++ newVars)
    HNothing                       -> applyHomomorphicRule sortOf allVars rule equations (equation:passedEqs)
    HFail                          -> Just ([], allVars)
  where
    applySubstitution subst = fmap (toLPETerm . applyVTerm subst . lTerm)

-- | Helper functions
---------------------

-- | @sortGreaterEq v t@ returns @True@ if the sort ensures that the sort of @v@ is greater or equal to
--   the sort of @t@.
sortCorrectForSubst :: IsConst c => (c -> LSort) -> LVar -> LTerm c -> Bool
sortCorrectForSubst st v t = sortCompare (lvarSort v) (sortOfLTerm st t) `elem` [Just EQ, Just GT]

occursVTermEqs :: IsConst c => LVar -> [Equal (LPETerm c)] -> Bool
occursVTermEqs v eqs = any (occursVTerm v . lTerm) (eqsToTerms eqs)

eqsToTerms :: [Equal a] -> [a]
eqsToTerms [] = []
eqsToTerms (e:es) = eqLHS e : eqRHS e : eqsToTerms es

foldVars :: IsConst c => [LTerm c] -> [LVar]
foldVars = sortednub . concatMap varsVTerm

getNewSimilarVar :: LVar -> [LVar] -> LVar
getNewSimilarVar x allVars = LVar (lvarName x) (lvarSort x) $ (+) 1 $ foldr (max . lvarIdx) (lvarIdx x) (filter (\e -> lvarName x == lvarName e) allVars)

-- | To Homomorphic Solved Form
-------------------------------

toHomomorphicSolvedForm :: IsConst c => (c -> LSort) -> [Equal (LTerm c)] -> Maybe [(LVar, LTerm c)]
toHomomorphicSolvedForm sortOf eqs = toFreeAvoid =<< toSubstForm sortOf eqs

toSubstForm :: IsConst c => (c -> LSort) -> [Equal (LTerm c)] -> Maybe [(LVar, LTerm c)]
toSubstForm sortOf eqs = let
  substWODubVars = map (moveVarLeft sortOf) $ filter (not . dubVars) eqs
  substM          = addOrderDubVars (unzip $ catMaybes substWODubVars) $ getDubVars eqs
  subst           = fromMaybe [] substM
  in if all isJust substWODubVars && isJust substM && sanityCheckUnification eqs && sanityCheckSolvedForm subst
  then Just subst
  else Nothing

dubVars :: IsConst c => Equal (LTerm c) -> Bool
dubVars (Equal l r) = case (viewTerm l, viewTerm r) of
  (Lit (Var lv), Lit (Var rv)) | lvarSort lv == lvarSort rv -> True
  _                                                         -> False

getDubVars :: IsConst c => [Equal (LTerm c)] -> [(LVar, LVar)]
getDubVars [] = []
getDubVars (Equal l r:es) = case (viewTerm l, viewTerm r) of
  (Lit (Var lv), Lit (Var rv)) | lvarSort lv == lvarSort rv -> (lv,rv):getDubVars es
  _                                                         -> getDubVars es

moveVarLeft :: IsConst c => (c -> LSort) -> Equal (LTerm c) -> Maybe (LVar, LTerm c)
moveVarLeft sortOf (Equal l r) = case (viewTerm l, viewTerm r) of
  (Lit (Var lv), Lit (Var rv)) | lvarSort lv == lvarSort rv                          -> error "moveVarLeft: Vars sort equal, no unique ordering"
  (Lit (Var lv), Lit (Var rv)) | sortCompare (lvarSort lv) (lvarSort rv) == Just GT  -> Just (lv, r)
  (Lit (Var lv), Lit (Var rv)) | sortCompare (lvarSort lv) (lvarSort rv) == Just LT  -> Just (rv, l)
  (Lit (Var lv), Lit (Var rv)) | isNothing $ sortCompare (lvarSort lv) (lvarSort rv) -> error "moveVarLeft: Uncomparable sorts should have been caught"
  (Lit (Var lv), _           ) | sortCorrectForSubst sortOf lv r                     -> Just (lv, r)
  (Lit (Var _ ), _           )                                                       -> error "moveVarLeft: Uncomparable sorts should have been caught"
  (_,            Lit (Var rv)) | sortCorrectForSubst sortOf rv l                     -> Just (rv, l)
  (_,            Lit (Var _ ))                                                       -> error "moveVarLeft: Uncomparable sorts should have been caught"
  (Lit (Con cl), Lit (Con cr)) | cl == cr                                            -> error "moveVarLeft: Equal consts should have dissapeared"
  (Lit (Con _ ), Lit (Con _ ))                                                       -> error "moveVarLeft: Unequal consts should have been caught"
  (Lit (Con _ ), _           )                                                       -> error "moveVarLeft: Const to Term not possible"
  (_,            Lit (Con _ ))                                                       -> error "moveVarLeft: Const to Term not possible"
  (FApp fl _,    FApp fr _   ) | fl == fr                                            -> error "moveVarLeft: Same functions not possible"
  -- This is allowed, as the unification algorithm can not fail on seeing equations like 
  -- pair(x1,x2) = henc(x3,x4) since with x1 = henc(x5,x4), x2 = henc(x6,x4) and x3 = pair(x5,x6)
  -- this is unifiable. However, we now know that these equalities don't exist or else varsub
  -- would have been applied.
  -- TODO: unification algorithm should be able to apply a rule to this
  -- (FApp _  _,    FApp _  _   ) | isPair l && isHomEnc r || isHomEnc l && isPair r    -> Nothing
  (FApp _  _,    FApp _  _   )                                                       -> error "moveVarLeft: Only different function symbols allowed are pair/henc"


addOrderDubVars :: IsConst c => ([LVar], [LTerm c]) -> [(LVar, LVar)] -> Maybe [(LVar, LTerm c)]
addOrderDubVars subst [] = Just (uncurry zip subst)
addOrderDubVars (lPVars, rPTerms) ((lv,rv):vvs) = let rPVars = foldVars rPTerms in 
  case (lv `elem` lPVars, lv `elem` rPVars, rv `elem` lPVars, rv `elem` rPVars) of
    (True,  True,  _,     _    ) -> error "orderDubVars: left var also on right side"
    (_,     _,     True,  True ) -> error "orderDubVars: left var also on right side"
    (True,  False, False, True ) -> error "orderDubVars: no duplicates" -- if getRightTerm lv == varTerm rv then addOrderDubVars (lPVars, rPTerms) vvs else Nothing
    (False, True,  True,  False) -> error "orderDubVars: no duplicates" -- if getRightTerm rv == varTerm lv then addOrderDubVars (lPVars, rPTerms) vvs else Nothing
    (True,  False, True,  False) -> if getRightTerm lv == getRightTerm rv then addOrderDubVars (lPVars, rPTerms) vvs else Nothing
    (False, True,  False, True ) -> error "orderDubVars: should not happen" -- addOrderDubVars (lv:rv:lPVars, nPT:nPT:map (applySubstToTerm [(lv,nPT),(rv,nPT)]) rPTerms) vvs
    (True,  False, False, False) -> addOrderDubVars (rv:lPVars, getRightTerm lv:rPTerms) vvs
    (False, False, True,  False) -> addOrderDubVars (lv:lPVars, getRightTerm rv:rPTerms) vvs
    (False, True,  False, False) -> addOrderDubVars (rv:lPVars, varTerm lv:rPTerms) vvs
    (False, False, False, True ) -> addOrderDubVars (lv:lPVars, varTerm rv:rPTerms) vvs
    (False, False, False, False) -> addOrderDubVars (lv:lPVars, varTerm rv:rPTerms) vvs -- TODO: other options possible
  where
    getRightTerm v = snd $ head $ filter (\s -> fst s == v) (zip lPVars rPTerms)

toFreeAvoid :: IsConst c => [(LVar, LTerm c)] -> Maybe [(LVar, LTerm c)]
toFreeAvoid subst = let
  (lVars, rTerms) = unzip subst
  freeAvoidingEqs = snd $ getFreeAvoidingSubstOfTerms (sortednub $ lVars ++ foldVars rTerms) rTerms []
  freeAvoidingSubst = freeAvoidingEqs ++ zip lVars (map (applySubstToTerm freeAvoidingEqs) rTerms)
  in if sanityCheckSolvedForm freeAvoidingSubst then Just freeAvoidingSubst else Nothing

getFreeAvoidingSubstOfTerms :: IsConst c => [LVar] -> [LTerm c] -> [(LVar, LTerm c)] -> ([LVar], [(LVar, LTerm c)])
getFreeAvoidingSubstOfTerms allVs terms newSubst = foldr (\t (vs,sbs) -> getFreeAvoidingSubstOfTerm vs t sbs) (allVs, newSubst) terms

getFreeAvoidingSubstOfTerm :: IsConst c => [LVar] -> LTerm c -> [(LVar, LTerm c)] -> ([LVar], [(LVar, LTerm c)])
getFreeAvoidingSubstOfTerm allVs t newSubst =
  case viewTerm t of
    (Lit (Con _)) -> (allVs, newSubst)
    (Lit (Var x)) -> if elem x $ map fst newSubst then (allVs, newSubst) else let newV = getNewSimilarVar x allVs in (newV:allVs, (x, varTerm newV):newSubst)
    (FApp _ args) -> getFreeAvoidingSubstOfTerms allVs args newSubst

applySubstToTerm :: IsConst c => [(LVar, LTerm c)] -> LTerm c -> LTerm c
applySubstToTerm newSubst t =
  case viewTerm t of
    (Lit (Var _))      -> foldl (\tOld (v,tNew) -> if tOld == varTerm v then tNew else tOld) t newSubst
    (Lit (Con _))      -> t
    (FApp funsym args) -> termViewToTerm $ FApp funsym $ map (applySubstToTerm newSubst) args

-- | Sanity check solved Form
-----------------------------

sanityCheckUnification :: IsConst c => [Equal (LTerm c)] -> Bool
sanityCheckUnification eqs = noDuplicates eqs || error "Sanity Check for Unification Algorithm failed"

sanityCheckSolvedForm :: IsConst c => [(LVar, LTerm c)] -> Bool
sanityCheckSolvedForm subst = (noDuplicatesSubst subst && allLeftVarsUnique subst && allLeftVarsNotRight subst) || error "Sanity Check for Solved Form failed"

noDuplicates :: IsConst c => [Equal (LTerm c)] -> Bool
noDuplicates [] = True
noDuplicates (Equal l1 r1:es) = not (any (\(Equal l2 r2) -> (l1 == l2 && r1 == r2) || (l1 == r2 && r1 == l2)) es) && noDuplicates es

noDuplicatesSubst :: IsConst c => [(LVar, LTerm c)] -> Bool
noDuplicatesSubst [] = True
noDuplicatesSubst ((l1,t1):substs) = not (any (\(l2,t2) -> (l1 == l2 && t1 == t2) || (varTerm l1 == t2 && t1 == varTerm l2)) substs) && noDuplicatesSubst substs

allLeftVarsUnique :: IsConst c => [(LVar, LTerm c)] -> Bool
allLeftVarsUnique [] = True
allLeftVarsUnique ((v1,_):substs) = not (any (\(v2,_) -> v1 == v2) substs) && allLeftVarsUnique substs

allLeftVarsNotRight :: IsConst c => [(LVar, LTerm c)] -> Bool
allLeftVarsNotRight subst = let (vars,terms) = unzip subst in not $ any (\v -> v `elem` foldVars terms) vars

-- Homomorphic Rules Managers
-----------------------------

-- | Return type for a HomomorphicRule
data HomomorphicRuleReturn c = 
    HEqs                 [Equal (LPETerm c)] [LVar]
  | HSubstEqs (LSubst c) [Equal (LPETerm c)] [LVar]
  | HNothing
  | HFail
  deriving (Show, Eq)

-- | Type for rules applied to equations for unification modulo EpsilonH
-- @arg1 = equation which we try to apply the rule on
-- @arg2 = translation from terms to sorts
-- @arg3 = all other equations (may be needed to check if a variable occurs in them)
type HomomorphicRule c = Equal (LPETerm c) -> (c -> LSort) -> [LVar] -> [Equal (LPETerm c)] -> HomomorphicRuleReturn c

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
  -- TODO: add normhomomorphic rule
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
combineWrapperHomomorphicRule rule1 rule2 eq sortOf allVars eqs =
  case rule1 eq sortOf allVars eqs of
    HEqs            newEqs newVars -> HEqs            newEqs newVars
    HSubstEqs subst newEqs newVars -> HSubstEqs subst newEqs newVars
    HNothing                       -> rule2 eq sortOf allVars eqs
    HFail                          -> HFail

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
trivialHomomorphicRule (Equal el er) _ _ = if lTerm el == lTerm er then HEqs [] else HNothing

stdDecompositionHomomorphicRule :: IsConst c => HomomorphicRule c
stdDecompositionHomomorphicRule (Equal el er) _ _ =
  case (viewTermPE el, viewTermPE er) of
    (FApp lfsym largs, FApp rfsym rargs) ->
      if lfsym == rfsym && length largs == length rargs
      then HEqs $ zipWith (\l r -> Equal (toLPETerm l) (toLPETerm r)) largs rargs
      else HNothing
    (_,_) -> HNothing

variableSubstitutionHomomorphicRule :: IsConst c => HomomorphicRule c
variableSubstitutionHomomorphicRule eq sortOf eqs = let eR = lTerm $ eqRHS eq in
  case (viewTermPE $ eqLHS eq, viewTermPE $ eqRHS eq) of
    (Lit (Var vl), Lit (Var vr)) | lvarSort vl == lvarSort vr ->
      if vl /= vr && occursVTermEqs vl eqs && occursVTermEqs vr eqs
      then HSubstEqs (Subst $ fromList [(vl, eR)]) [eq]
      else HNothing
    (Lit (Var vl), _) ->
      if not (occursVTerm vl eR) && occursVTermEqs vl eqs && sortCorrectForSubst sortOf vl eR
      then HSubstEqs (Subst $ fromList [(vl, eR)]) [eq]
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

-- | Newly added rule
---------------------

differentConsts :: IsConst c => HomomorphicRule c
differentConsts (Equal el er) _ _ = case (viewTermPE el, viewTermPE er) of
  (Lit (Con cl), Lit (Con cr)) -> if cl == cr then HNothing else HFail
  (Lit (Con _ ), Lit (Var _ )) -> HNothing -- 
  (Lit (Con _ ), _           ) -> HFail -- TODO: not true if const is public sort and right side public sort what then?
  (Lit (Var _ ), Lit (Con _ )) -> HNothing
  (_,            Lit (Con _ )) -> HFail
  _                            -> HNothing

doSortsCompare :: IsConst c => HomomorphicRule c
doSortsCompare (Equal el er) sortOf _ = case (viewTermPE el, viewTermPE er) of
  (Lit (Var vl), Lit (Var vr)) -> if sortCorrectForSubst sortOf vl (lTerm er) || sortCorrectForSubst sortOf vr (lTerm el) then HNothing else HFail
  (Lit (Var vl), _           ) -> if sortCorrectForSubst sortOf vl (lTerm er) then HNothing else HFail
  (_,            Lit (Var vr)) -> if sortCorrectForSubst sortOf vr (lTerm el) then HNothing else HFail
  -- TODO: can be done better, if consts then ??
  _                            -> if isJust $ sortCompare (sortOfLTerm sortOf $ lTerm el) (sortOfLTerm sortOf $ lTerm er) then HNothing else HFail

-- | Homomorphic Patterns
-------------------------

shapingHomomorphicRule :: IsConst c => HomomorphicRule c
shapingHomomorphicRule eq _ eqs = let
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
      -- TODO: change to name of x ??
      xFresh = varTerm $ getNewSimilarVar (LVar "x" LSortMsg 0) (foldVars $ eqsToTerms $ map (fmap lTerm) (eq:eqs)) 
      lhs1NewETerm = ([xFresh] ++ take (m-1) (tail eRepRHS) ++ tail qualifyingELhs)
      lhs1NewPTerm = let (ys,zs) = splitAt qualifyingIndex eRepsLHS in
        PRep strsLHS (ys ++ [lhs1NewETerm] ++ tail zs)
      lhs1 = toLPETerm $ fromPRepresentation lhs1NewPTerm
      rhs2 = toLPETerm $ fromERepresentation $ xFresh : take (m-1) (tail eRepRHS)
      in HEqs [Equal lhs1 (eqRHS eq), Equal (toLPETerm x) rhs2]
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
  in if any (\e -> not (isVar $ head e) && (length e < n + 1)) eRepsLHS
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
  then HEqs $ Equal newLHS newRHS : getAllCombinations allKms
  else HNothing
  where
    getAllCombinations :: IsConst c => [LPETerm c] -> [Equal (LPETerm c)]
    getAllCombinations [] = []
    getAllCombinations (x:xs) = pairCombinations x xs ++ getAllCombinations xs
    pairCombinations _ [] = []
    pairCombinations x (y:ys) = Equal x y : pairCombinations x ys