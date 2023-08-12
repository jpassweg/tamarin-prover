module Term.Homomorphism.Unification (
  -- * Unification modulo EpsilonH for Homomorphic Encryption
  unifyHomomorphicLTerm
  
  -- * Maude wrappers
  , unifyHomomorphicLTermWithMaude
  , unifyHomomorphicLTermFactored

  -- * For debugging
  , debugHomomorphicRule
  , HomomorphicRuleReturn(..)
) where

import qualified Data.Map as M
import Control.Monad.RWS (reader)

import Term.Homomorphism.LPETerm

import Term.LTerm (
  LTerm, Lit(Var, Con), IsConst, LVar(..), 
  termVar, isVar, varTerm, occursVTerm, varsVTerm,
  TermView(FApp, Lit), viewTerm, termViewToTerm, isPair,
  LSort(..), sortCompare, sortOfLTerm)
-- Lit(Var, Con), IsConst, isVar, varTerm, termVar, varsVTerm, occursVTerm come from Term.VTerm
-- isPair come from Term.Term
-- TermView(Lit, FApp), viewTerm, termViewToTerm come from Term.Term.Raw

import Term.Rewriting.Definitions (Equal(..))
import Term.Substitution.SubstVFree (LSubst, Subst(..), emptySubst, applyVTerm)
import Term.Substitution.SubstVFresh (SubstVFresh(..))
import Term.Maude.Process (WithMaude)
import Debug.Trace.Ignore (trace)

-- Unification Algorithm using the Homomorphic Rules
----------------------------------------------------

-- | Homomorphic encryption wrapper
unifyHomomorphicLTermFactored :: (IsConst c) => (c -> LSort) -> [Equal (LTerm c)] -> WithMaude (LSubst c, [SubstVFresh c LVar])
unifyHomomorphicLTermFactored sortOf eqs = (\s -> (emptySubst,s)) <$> unifyHomomorphicLTermWithMaude sortOf eqs

-- | Homomorphic encryption wrapper
unifyHomomorphicLTermWithMaude :: (IsConst c) => (c -> LSort) -> [Equal (LTerm c)] -> WithMaude [SubstVFresh c LVar]
unifyHomomorphicLTermWithMaude sortOf eqs = 
  reader $ \_ -> (\res -> 
    trace (unlines $ ["unifyLTerm: "++ show eqs, "result = "++  show res]) res) $ subst
  where
    subst = map (\s -> case s of Subst s' -> SubstVFresh s') $ unifyHomomorphicLTerm sortOf eqs

-- | @unifyHomomorphicLNTerm eqs@ returns a set of unifiers for @eqs@ modulo EpsilonH.
-- returns a substitution for terms so that they unify or an empty list 
-- if it is not possible to unify the terms
-- Types used:
-- LNTerm = Term (Lit (Con Name | Var LVar) | FApp FunSym [Term Lit ((Con Name | Var LVar))])
-- use viewTerm to use "case of" term
-- Equal LNTerm = Equal { eqLHS :: LNTerm, eqRHS :: LNTerm }
-- sortOfName :: Name -> LSort
-- data LSort = LSortPub | LSortFresh | LSortMsg | LSortNode -- Nodes are for dependency graphs
unifyHomomorphicLTerm :: (IsConst c) => (c -> LSort) -> [Equal (LTerm c)] -> [LSubst c]
unifyHomomorphicLTerm sortOf eqs =
  toSubst $ applyHomomorphicRules sortOf allHomomorphicRules (map (fmap toLPETerm) eqsN)
  where 
    eqsN = map (fmap normHomomorphic) eqs
    toSubst [] = 
      if and $ map (\eq -> (eqLHS eq) == (eqRHS eq)) eqsN
      then [emptySubst]
      else []
    toSubst eqsSubst = case toHomomorphicSolvedForm sortOf (map (fmap lTerm) eqsSubst) of
      Just normEqsSubst -> [Subst $ M.fromList $ map getLeftVar normEqsSubst]
      Nothing -> []
    getLeftVar e = case termVar $ eqLHS e of
      Just v ->  (v, eqRHS e)
      Nothing -> (LVar "VARNOTFOUND" LSortFresh 0, eqRHS e)

-- | Applies all homomorphic rules given en block, i.e., 
-- it applies the first rule always first after each change
applyHomomorphicRules :: (IsConst c) => (c -> LSort) -> [HomomorphicRule c] -> [Equal (LPETerm c)] -> [Equal (LPETerm c)]
applyHomomorphicRules _ [] eqs = eqs -- no more rules to apply 
applyHomomorphicRules sortOf (rule:rules) eqs =
  case applyHomomorphicRule rule sortOf eqs [] of
    Just newEqs -> applyHomomorphicRules sortOf allHomomorphicRules newEqs
    Nothing     -> applyHomomorphicRules sortOf rules eqs

-- | Applies the homomorphic rule to the first term possible in equation list or returns Nothing 
-- if the rule is not applicable to any terms
applyHomomorphicRule :: (IsConst c) => HomomorphicRule c -> (c -> LSort) -> [Equal (LPETerm c)] -> [Equal (LPETerm c)] -> Maybe [Equal (LPETerm c)]
applyHomomorphicRule _ _ [] _ = Nothing
applyHomomorphicRule rule sortOf (equation:equations) passedEqs =
  case rule equation sortOf (passedEqs ++ equations) of
    HEqs newEqs ->            Just (passedEqs ++ newEqs ++ equations)
    HSubstEqs subst newEqs -> Just $ (map (applySubstitution subst) (passedEqs ++ equations)) ++ newEqs
    HNothing ->               applyHomomorphicRule rule sortOf equations (equation:passedEqs)
    HFail ->                  Just []
  where
    applySubstitution subst eq = Equal 
      (toLPETerm $ applyVTerm subst $ lTerm $ eqLHS eq) 
      (toLPETerm $ applyVTerm subst $ lTerm $ eqRHS eq)

-- Transforms equations to Homomorphic Solved Form
-- Returns Nothing if it is not possible to put the equations Homomorphic Solved Form
-- This function does not change the equations themselves, but assures that the variables
-- on the left side of all equations are unique.
toHomomorphicSolvedForm :: (IsConst c) => (c -> LSort) -> [Equal (LTerm c)] -> Maybe [Equal (LTerm c)]
toHomomorphicSolvedForm sortOf eqs = let
  varLeftEqs = map moveVarLeft eqs
  vLEqsNoDups = removeDuplicates varLeftEqs
  doubleVarEqs = filter doubleVarEq vLEqsNoDups
  singleVarEqs = filter (not . doubleVarEq) vLEqsNoDups
  sLeftVars = map eqLHS singleVarEqs
  sRightTerms = map eqRHS singleVarEqs
  orderedDVarEqs = orderDoubleVarEqs sortOf doubleVarEqs (sLeftVars ++ sRightTerms)
  dLeftVars = map eqLHS orderedDVarEqs
  dRightTerms = map eqRHS orderedDVarEqs
  leftVars = sLeftVars ++ dLeftVars
  rightTerms = sRightTerms ++ dRightTerms
  allVars = foldVars (leftVars ++ rightTerms)
  freeAvoidingEqs = snd $ getFreeAvoidingEqsOfTerms allVars rightTerms []
  freeAvoidedRightTerms = applyEqsToTerms freeAvoidingEqs rightTerms
  freeAvoidedEqs = (zipWith Equal leftVars freeAvoidedRightTerms)
  completeSubstitution = freeAvoidingEqs ++ freeAvoidedEqs
  in if (allLeftVarsUnique leftVars)
    && (allLeftVarsNotRight leftVars rightTerms)
    && (sortCorrectEqs sortOf completeSubstitution)
  then Just completeSubstitution
  else Nothing
  where
    moveVarLeft :: (IsConst c) => Equal (LTerm c) -> Equal (LTerm c)
    moveVarLeft e =
      case (viewTerm $ eqLHS e, viewTerm $ eqRHS e) of 
        (FApp _ _,    Lit (Var _)) -> Equal (eqRHS e) (eqLHS e)
        (Lit (Con _), Lit (Var _)) -> Equal (eqRHS e) (eqLHS e)
        (_, _)                     -> Equal (eqLHS e) (eqRHS e)
    removeDuplicates :: (IsConst c) => [Equal (LTerm c)] -> [Equal (LTerm c)]
    removeDuplicates [] = []
    removeDuplicates (e:es) = if any (\e2 -> 
         ((eqLHS e) == (eqLHS e2) && (eqRHS e) == (eqRHS e2))
      || ((eqLHS e) == (eqRHS e2) && (eqRHS e) == (eqLHS e2))) es
      then es
      else e:(removeDuplicates es)
    doubleVarEq :: (IsConst c) => Equal (LTerm c) -> Bool
    doubleVarEq e = 
      case (viewTerm $ eqLHS e, viewTerm $ eqRHS e) of
        (Lit (Var _), Lit (Var _)) -> True
        (_, _)                     -> False
    allLeftVarsUnique :: (IsConst c) => [LTerm c] -> Bool
    allLeftVarsUnique [] = True
    allLeftVarsUnique (l:ls) = (varNotPartOfTerms l ls) && (allLeftVarsUnique ls)
    -- can be improved by precomputing all variables and then only checking if inside list
    allLeftVarsNotRight :: (IsConst c) => [LTerm c] -> [LTerm c] -> Bool
    allLeftVarsNotRight [] _ = True
    allLeftVarsNotRight (l:ls) rs = (varNotPartOfTerms l rs) && (allLeftVarsNotRight ls rs)
    orderDoubleVarEqs :: (IsConst c) => (c -> LSort) -> [Equal (LTerm c)] -> [LTerm c] -> [Equal (LTerm c)]
    orderDoubleVarEqs _ [] _ = []
    orderDoubleVarEqs sortOf' (e:es) rs = let 
      rsPlusEs = rs ++ (eqsToTerms es) 
      rsPlusE = rs ++ [(eqLHS e), (eqRHS e)] 
      in case (varNotPartOfTerms (eqLHS e) rsPlusEs, varNotPartOfTerms (eqRHS e) rsPlusEs) of
        (True,True) -> if sortCompare 
          (sortOfLTerm sortOf' (eqLHS e)) (sortOfLTerm sortOf' (eqRHS e)) `elem` [Just EQ, Just GT]
          then e : (orderDoubleVarEqs sortOf' es rsPlusE)
          else (Equal (eqRHS e) (eqLHS e)) : (orderDoubleVarEqs sortOf' es rsPlusE)
        (True, _)   -> e : (orderDoubleVarEqs sortOf' es rsPlusE)
        (_, True)   -> (Equal (eqRHS e) (eqLHS e)) : (orderDoubleVarEqs sortOf' es rsPlusE)
        (_,_)       -> e : (orderDoubleVarEqs sortOf' es rsPlusE)
    eqsToTerms :: (IsConst c) => [Equal (LTerm c)] -> [(LTerm c)]
    eqsToTerms [] = []
    eqsToTerms (e:es) = [eqLHS e, eqRHS e] ++ (eqsToTerms es)
    varNotPartOfTerms :: (IsConst c) => LTerm c -> [LTerm c] -> Bool
    varNotPartOfTerms _ [] = True
    varNotPartOfTerms l (r:rs) = 
      case (viewTerm l) of
        (Lit (Var _)) -> (varNotPartOfTerm l r) && (varNotPartOfTerms l rs)
        (_)           -> False
    varNotPartOfTerm :: (IsConst c) => LTerm c -> LTerm c -> Bool
    varNotPartOfTerm l r =
      case (viewTerm r) of
        (FApp _ args) -> all (varNotPartOfTerm l) args
        (Lit (Var _)) -> l /= r
        (Lit (Con _)) -> True
    foldVars :: (IsConst c) => [LTerm c] -> [LVar]
    foldVars ts = concat $ map varsVTerm ts
    getFreeAvoidingEqsOfTerms :: (IsConst c) => [LVar] -> [LTerm c] -> [Equal (LTerm c)] -> ([LVar], [Equal (LTerm c)])
    getFreeAvoidingEqsOfTerms allVs [] newEs = (allVs, newEs)
    getFreeAvoidingEqsOfTerms allVs (t:ts) newEs =
      let (nV, nEs) = getFreeAvoidingEqsOfTerm allVs t newEs 
      in getFreeAvoidingEqsOfTerms nV ts nEs
    getFreeAvoidingEqsOfTerm :: (IsConst c) => [LVar] -> LTerm c -> [Equal (LTerm c)] -> ([LVar], [Equal (LTerm c)])
    getFreeAvoidingEqsOfTerm allVs t newEs =
      case viewTerm t of
        (Lit (Con _)) -> (allVs, newEs)
        (Lit (Var x)) -> if t /= (applyEqsToTerm newEs t)
          then (allVs, newEs)
          else let newV = getNewVar allVs x in (newV:allVs, (Equal t $ varTerm newV):newEs)
        (FApp _ args) -> getFreeAvoidingEqsOfTerms allVs args newEs
    getNewVar :: [LVar] -> LVar -> LVar
    getNewVar allVs x = LVar (lvarName x) (lvarSort x) 
      $ (+) 1
      $ foldr max (lvarIdx x) 
      $ map (\e -> lvarIdx e) 
      $ filter (\e -> lvarName x == lvarName e) allVs
    applyEqsToTerms :: (IsConst c) => [Equal (LTerm c)] -> [LTerm c] -> [LTerm c]
    applyEqsToTerms _ [] = []
    applyEqsToTerms newEs (t:ts) = (applyEqsToTerm newEs t):(applyEqsToTerms newEs ts)
    applyEqsToTerm :: (IsConst c) => [Equal (LTerm c)] -> LTerm c -> LTerm c
    applyEqsToTerm newEs t =
      case viewTerm t of
        (Lit (Var _)) -> foldr applyEqToTerm t newEs
        (Lit (Con _)) -> t
        (FApp funsym args) -> 
          termViewToTerm $ FApp funsym $ map (applyEqsToTerm newEs) args
    applyEqToTerm :: (IsConst c) => Equal (LTerm c) -> LTerm c -> LTerm c
    applyEqToTerm e t = if t == eqLHS e then eqRHS e else t
    sortCorrectEqs :: (IsConst c) => (c -> LSort) -> [Equal (LTerm c)] -> Bool
    sortCorrectEqs sortOf' es = all (sortCorrectEq sortOf') es
    sortCorrectEq :: (IsConst c) => (c -> LSort) -> Equal (LTerm c) -> Bool
    sortCorrectEq sortOf' (Equal l r) = 
      case (sortOfLTerm sortOf' l, sortOfLTerm sortOf' r) of
        (sl, sr) | sl == sr -> True
        (LSortNode, _)      -> False
        (_, LSortNode)      -> False
        (sl, sr)            -> sortCompare sl sr `elem` [Just EQ, Just GT]

-- Homomorphic Rules Managers
-----------------------------

-- | Return type for a HomomorphicRule
data HomomorphicRuleReturn c = HEqs [Equal (LPETerm c)] 
  | HSubstEqs (LSubst c) [Equal (LPETerm c)] 
  | HNothing
  | HFail
  deriving (Show, Eq)

-- | Type for rules applied to equations for unification modulo EpsilonH
-- @arg1 = equation which we try to apply the rule on
-- @arg2 = translation from terms to sorts
-- @arg3 = all other equations (may be needed to check if a variable occurs in them)
type HomomorphicRule c = Equal (LPETerm c) -> (c -> LSort) -> [Equal (LPETerm c)] -> HomomorphicRuleReturn c

-- | All homomorphic rules in order of application
-- All rules are added as such that they are first applied on the equation
-- Equal (eqLHS eq) (eqRHS eq) and then on the equation Equal (eqRHS eq) (eqLHS eq)
-- with eq being the first argument given to the function
allHomomorphicRules :: (IsConst c) => [HomomorphicRule c]
allHomomorphicRules = map (\r -> combineWrapperHomomorphicRule r (switchedWrapperHomomorphicRule r)) 
  -- failure rules first
  [ failureOneHomomorphicRule 
  , failureTwoHomomorphicRule
  , occurCheckHomomorphicRule
  , clashHomomorphicRule 
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
combineWrapperHomomorphicRule :: (IsConst c) => HomomorphicRule c -> HomomorphicRule c -> HomomorphicRule c
combineWrapperHomomorphicRule rule1 rule2 eq sortOf eqs =
  case rule1 eq sortOf eqs of
    HEqs newEqs             -> HEqs newEqs
    HSubstEqs subst newEqs  -> HSubstEqs subst newEqs
    HNothing                -> rule2 eq sortOf eqs
    HFail                   -> HFail

-- | Since the equality sign used is not oriented, we need
-- to look at the possibility of rule applications for 
-- both x = t and t = x for any equation.
-- This function is used in combination with combineWrapperHomomorphicRule
switchedWrapperHomomorphicRule :: (IsConst c) => HomomorphicRule c -> HomomorphicRule c
switchedWrapperHomomorphicRule rule eq sortOf eqs =
  rule (Equal (eqRHS eq) (eqLHS eq)) sortOf eqs

-- | used to export homomorphic rules for debugging
debugHomomorphicRule :: (IsConst c) => Int -> HomomorphicRule c
debugHomomorphicRule i eq sortOf eqs =
  (allHomomorphicRules !! i) eq sortOf eqs

-- | Standard syntatictic inference rules
-----------------------------------------

trivialHomomorphicRule :: (IsConst c) => HomomorphicRule c
trivialHomomorphicRule eq _ _ = if (lTerm $ eqLHS eq) == (lTerm $ eqRHS eq)
  then HEqs []
  else HNothing

stdDecompositionHomomorphicRule :: (IsConst c) => HomomorphicRule c
stdDecompositionHomomorphicRule eq _ _ =
  case (viewTerm $ lTerm $ eqLHS eq, viewTerm $ lTerm $ eqRHS eq) of
    (FApp lfsym largs, FApp rfsym rargs) -> 
      if (lfsym == rfsym && length largs == length rargs) 
      then HEqs $ map (\(a,b) -> Equal (toLPETerm a) (toLPETerm b)) $ zip largs rargs
      else HNothing
    (_,_) -> HNothing

variableSubstitutionHomomorphicRule :: (IsConst c) => HomomorphicRule c
variableSubstitutionHomomorphicRule eq _ eqs =
  case (viewTerm $ lTerm $ eqLHS eq, viewTerm $ lTerm $ eqRHS eq) of
    (Lit (Var _), Lit (Var _)) -> HNothing
    (Lit (Var vl), _) -> 
      if (not $ occursVTerm vl (lTerm $ eqRHS eq)) && (occursEqs vl eqs) 
      then HSubstEqs (Subst $ M.fromList [(vl, lTerm $ eqRHS eq)]) [eq]
      else HNothing
    _ -> HNothing
  where
    occursEqs v es = any (\(Equal a b) -> (occursVTerm v $ lTerm a) || (occursVTerm v $ lTerm b)) es

clashHomomorphicRule :: (IsConst c) => HomomorphicRule c
clashHomomorphicRule eq _ _ = let
    tL = lTerm $ eqLHS eq
    tR = lTerm $ eqRHS eq
  in case (viewTerm tL, viewTerm tR) of
    (FApp lfsym _, FApp rfsym _) -> 
      if lfsym == rfsym || (isPair tL && isHenc rfsym) || (isHenc lfsym && isPair tR)
      then HNothing
      else HFail
    (_,_) -> HNothing

occurCheckHomomorphicRule :: (IsConst c) => HomomorphicRule c
occurCheckHomomorphicRule eq _ _ = 
  case termVar $ lTerm $ eqLHS eq of
    Just v  -> if 
        ((lTerm $ eqLHS eq) /= (lTerm $ eqRHS eq))
        && (occursVTerm v (lTerm $ eqRHS eq))
      then HFail
      else HNothing
    Nothing -> HNothing

-- | Homomorphic Patterns
-------------------------

shapingHomomorphicRule :: (IsConst c) => HomomorphicRule c
shapingHomomorphicRule eq _ eqs = let
  eRepsLHS = eRepsTerms $ pRep $ eqLHS eq
  strsLHS = eRepsString $ pRep $ eqLHS eq
  eRepRHS = eRep $ eqRHS eq
  n = (length $ eRepRHS) - 1
  in if (length $ eRepsLHS) >= 1 && n >= 2
  then case findQualifyingETerm eRepsLHS n 0 of
    Just qualifyingIndex -> let 
      qualifyingELhs = eRepsLHS !! qualifyingIndex
      m = n + 2 - (length qualifyingELhs)
      xnew = varTerm $ LVar "fxShapingHomomorphic" LSortFresh $ gC ([eq] ++ eqs)
      x = toLPETerm $ head qualifyingELhs
      lhs1NewETerm = ([xnew] ++ (take (m-1) (tail eRepRHS)) ++ (tail qualifyingELhs))
      lhs1NewPTerm = let (ys,zs) = splitAt qualifyingIndex eRepsLHS in
        PRep strsLHS (ys ++ [lhs1NewETerm] ++ (tail zs))
      lhs1 = toLPETerm $ fromPRepresentation lhs1NewPTerm
      rhs2 = toLPETerm $ fromERepresentation $ [xnew] ++ (take (m-1) (tail eRepRHS))
      in HEqs [Equal lhs1 (eqRHS eq), Equal x rhs2] 
    Nothing -> HNothing
  else HNothing
  where
    findQualifyingETerm :: (IsConst c) => [ERepresentation c] -> Int -> Int -> Maybe Int
    findQualifyingETerm [] _ _ = Nothing
    findQualifyingETerm (e:es) n ind =
      if (length e <= n) && (length e >= 2) && (isVar $ head e)
      then Just ind
      else findQualifyingETerm es n (ind+1)
    gC :: (IsConst c) => [Equal (LPETerm c)] -> Integer
    gC qs = (gC' qs 0) + 1
    gC' :: (IsConst c) => [Equal (LPETerm c)] -> Integer -> Integer
    gC' [] num = num
    gC' (q:qs) num = gC' qs $ max num (maxQ q)
    maxQ :: (IsConst c) => Equal (LPETerm c) -> Integer
    maxQ q = foldr max 0
      $ map lvarIdx
      $ filter (\lv -> lvarName lv == "fxShapingHomomorphic")
      $ (varsVTerm $ lTerm $ eqLHS q) ++ (varsVTerm $ lTerm $ eqRHS q)

failureOneHomomorphicRule :: (IsConst c) => HomomorphicRule c
failureOneHomomorphicRule eq _ _ = let
    t1 = lTerm $ eqLHS eq
    t2 = lTerm $ eqRHS eq
    t1Pos = positionsWithTerms t1
    t2Pos = positionsWithTerms t2
    t1NonKey = filter (\(p,_) -> all ((==) '1') (ePosition p t1)) t1Pos
    t2NonKey = filter (\(p,_) -> all ((==) '1') (ePosition p t2)) t2Pos
    matchedVars = matchVars t1NonKey t2NonKey
  in if (t1 /= t2) && any (\(m1,m2) -> positionsIncompatible m1 t1 m2 t2) matchedVars
  then HFail
  else HNothing
  where 
    matchVars :: (IsConst c) => [(String, (LTerm c))] -> [(String, (LTerm c))] -> [(String, String)]
    matchVars [] _ = []
    matchVars _ [] = []
    matchVars (v:vs) vs2 =
      let matches = filter (\vv2 -> (snd v) == (snd vv2)) vs2 in
      if (isVar $ snd v) && (not $ null matches)
      then (map (\(m,_) -> (fst v, m)) matches) ++ matchVars vs vs2
      else matchVars vs vs2

failureTwoHomomorphicRule :: (IsConst c) => HomomorphicRule c
failureTwoHomomorphicRule eq _ _ = let 
  n = (length $ eRep $ eqRHS eq) - 1 
  eRepsLHS = eRepsTerms $ pRep $ eqLHS eq
  in if any (\e -> (not $ isVar $ head $ e) && (length e < n + 1)) eRepsLHS
  then HFail
  else HNothing

parsingHomomorphicRule :: (IsConst c) => HomomorphicRule c
parsingHomomorphicRule eq _ _ = let
  eRepsLHS = eRepsTerms $ pRep $ eqLHS eq
  strRepsLHS = eRepsString $ pRep $ eqLHS eq
  newERepsLHS = map init eRepsLHS
  eRepRHS = eRep $ eqRHS eq
  newLHS = toLPETerm $ fromPRepresentation $ PRep strRepsLHS newERepsLHS
  newRHS = toLPETerm $ fromERepresentation $ init eRepRHS
  allKms = map toLPETerm $ [last eRepRHS] ++ (map last eRepsLHS)
  in if all (\t -> length t >= 2) (eRepsLHS ++ [eRepRHS])
  then HEqs $ [Equal newLHS newRHS] ++ (getAllCombinations allKms) 
  else HNothing
  where
    getAllCombinations :: (IsConst c) => [LPETerm c] -> [Equal (LPETerm c)]
    getAllCombinations [] = []
    getAllCombinations (x:xs) = pairCombinations x xs ++ getAllCombinations xs
    pairCombinations _ [] = []
    pairCombinations x (y:ys) = [Equal x y] ++ pairCombinations x ys