module Term.Homomorphism.Unification (
  -- * Unification modulo EpsilonH for Homomorphic Encryption
  unifyHomomorphicLNTerm

  -- * For debugging
  , debugHomomorphicRule
  , HomomorphicRuleReturn(..)
  , normHomomorphic
) where

import qualified Data.Map                         as M
import Term.Homomorphism.LNPETerm
import Term.Rewriting.Definitions
import Term.Substitution.SubstVFree
import Term.Term.FunctionSymbols

import Term.LTerm

-- Unification modulo EpsilonH
----------------------------------------------------------------------

-- | Return type for a HomomorphicRule
data HomomorphicRuleReturn = HEqs [Equal LNPETerm] 
  | HSubstEqs LNSubst [Equal LNPETerm] 
  | HNothing
  | HFail
  deriving (Show, Eq)

-- | Type for rules applied to equations for unification modulo EpsilonH
type HomomorphicRule = Equal LNPETerm -> (Name -> LSort) -> [Equal LNPETerm] -> HomomorphicRuleReturn

-- | All homomorphic rules in order of application
allHomomorphicRules :: [HomomorphicRule]
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
  , stdDecompositionHomomorphicRule]

-- | Combines two rules and runs one after the other if the first returns HNothing
combineWrapperHomomorphicRule :: HomomorphicRule -> HomomorphicRule -> HomomorphicRule
combineWrapperHomomorphicRule rule1 rule2 eq sortOf eqs =
  case rule1 eq sortOf eqs of
    HEqs newEqs             -> HEqs newEqs
    HSubstEqs subst newEqs  -> HSubstEqs subst newEqs
    HNothing                -> rule2 eq sortOf eqs
    HFail                   -> HFail

-- | Since the equality sign used is not oriented, we need
-- to look at the possibility of rule applications for 
-- both x = t and t = x for any equation.
switchedWrapperHomomorphicRule :: HomomorphicRule -> HomomorphicRule
switchedWrapperHomomorphicRule rule eq sortOf eqs =
  rule (Equal (eqRHS eq) (eqLHS eq)) sortOf eqs

-- | used to export homomorphic rules for debugging
debugHomomorphicRule :: Int -> HomomorphicRule
debugHomomorphicRule i eq sortOf eqs =
  (allHomomorphicRules !! i) eq sortOf eqs

-- | Standard syntatictic inference rules
-----------------------------------------

trivialHomomorphicRule :: HomomorphicRule
trivialHomomorphicRule eq _ _ = if (lnTerm $ eqLHS eq) == (lnTerm $ eqRHS eq)
  then HEqs []
  else HNothing

stdDecompositionHomomorphicRule :: HomomorphicRule
stdDecompositionHomomorphicRule eq _ _ =
  case (viewTerm $ lnTerm $ eqLHS eq, viewTerm $ lnTerm $ eqRHS eq) of
    (FApp (NoEq lfsym) largs, FApp (NoEq rfsym) rargs) -> 
      addArgs (lfsym == rfsym && length largs == length rargs) largs rargs 
    (FApp List largs, FApp List rargs)                 -> 
      addArgs (length largs == length rargs) largs rargs
    (FApp (AC lacsym) largs, FApp (AC racsym) rargs)   -> 
      addArgs (lacsym == racsym && length largs == length rargs) largs rargs
    (FApp (C lcsym) largs, FApp (C rcsym) rargs)       -> 
      addArgs (lcsym == rcsym && length largs == length rargs) largs rargs
    (_,_)                                              -> HNothing
  where
    addArgs bool las ras = 
      if bool
      then HEqs $ map (\(a,b) -> Equal (toLNPETerm a) (toLNPETerm b)) $ zip las ras
      else HNothing

-- NOTE: might need to check if the substitution this function is returning
-- does not violate rules about which sort of variables are allowed to be
-- substituted.
variableSubstitutionHomomorphicRule :: HomomorphicRule
variableSubstitutionHomomorphicRule eq _ eqs =
  case (viewTerm $ lnTerm $ eqLHS eq, viewTerm $ lnTerm $ eqRHS eq) of
    (Lit (Var _), Lit (Var _)) -> HNothing
    (Lit (Var vl), _) -> 
      if (not $ occursVTerm vl (lnTerm $ eqRHS eq)) && (occursEqs vl eqs) 
      then HSubstEqs (Subst $ M.fromList [(vl, lnTerm $ eqRHS eq)]) [eq]
      else HNothing
    _ -> HNothing
  where
    occursEqs v es = 
      any (\(Equal a b) -> (occursVTerm v $ lnTerm a) || 
                           (occursVTerm v $ lnTerm b)) es

clashHomomorphicRule :: HomomorphicRule
clashHomomorphicRule eq _ _ = 
  case (viewTerm $ lnTerm $ eqLHS eq, viewTerm $ lnTerm $ eqRHS eq) of
    (FApp (NoEq lfsym) _, FApp (NoEq rfsym) _) -> 
      if lfsym == rfsym 
        || (lfsym == pairSym && isHenc (NoEq rfsym))
        || (isHenc (NoEq lfsym) && rfsym == pairSym)
      then HNothing
      else HFail
    (FApp List _, FApp List _)                 -> HNothing
    (FApp (AC lacsym) _, FApp (AC racsym) _)   -> 
      if lacsym == racsym
      then HNothing
      else HFail
    (FApp (C lcsym) _, FApp (C rcsym) _)       -> 
      if lcsym == rcsym
      then HNothing
      else HFail
    (_,_)                                      -> HNothing

occurCheckHomomorphicRule :: HomomorphicRule
occurCheckHomomorphicRule eq _ _ = 
  case getVar $ lnTerm $ eqLHS eq of
    Just v  -> if 
        ((lnTerm $ eqLHS eq) /= (lnTerm $ eqRHS eq))
        && (occursVTerm v (lnTerm $ eqRHS eq))
      then HFail
      else HNothing
    Nothing -> HNothing

-- | Homomorphic Patterns
-------------------------

shapingHomomorphicRule :: HomomorphicRule
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
      x = toLNPETerm $ head qualifyingELhs
      lhs1NewETerm = ([xnew] ++ (take (m-1) (tail eRepRHS)) ++ (tail qualifyingELhs))
      lhs1NewPTerm = let (ys,zs) = splitAt qualifyingIndex eRepsLHS in
        PRep strsLHS (ys ++ [lhs1NewETerm] ++ (tail zs))
      lhs1 = toLNPETerm $ fromPRepresentation lhs1NewPTerm
      rhs2 = toLNPETerm $ fromERepresentation $ [xnew] ++ (take (m-1) (tail eRepRHS))
      in HEqs [Equal lhs1 (eqRHS eq), Equal x rhs2] 
    Nothing -> HNothing
  else HNothing
  where
    findQualifyingETerm :: [ERepresentation] -> Int -> Int -> Maybe Int
    findQualifyingETerm [] _ _ = Nothing
    findQualifyingETerm (e:es) n ind =
      if (length e <= n) && (length e >= 2) && (isVar $ head e)
      then Just ind
      else findQualifyingETerm es n (ind+1)
    gC :: [Equal LNPETerm] -> Integer
    gC qs = (gC' qs 0) + 1
    gC' :: [Equal LNPETerm] -> Integer -> Integer
    gC' [] num = num
    gC' (q:qs) num = gC' qs $ max num (maxQ q)
    maxQ :: Equal LNPETerm -> Integer
    maxQ q = foldr max 0
      $ map lvarIdx
      $ filter (\lv -> lvarName lv == "fxShapingHomomorphic")
      $ (frees $ lnTerm $ eqLHS q) ++ (frees $ lnTerm $ eqRHS q)

failureOneHomomorphicRule :: HomomorphicRule
failureOneHomomorphicRule eq _ _ = let
    t1 = lnTerm $ eqLHS eq
    t2 = lnTerm $ eqRHS eq
    t1Pos = positionsWithTerms t1
    t2Pos = positionsWithTerms t2
    t1NonKey = filter (\(p,_) -> all ((==) '1') (ePosition p t1)) t1Pos
    t2NonKey = filter (\(p,_) -> all ((==) '1') (ePosition p t2)) t2Pos
    matchedVars = matchVars t1NonKey t2NonKey
  in if (t1 /= t2) 
    && any (\(m1,m2) -> positionsIncompatible m1 t1 m2 t2) matchedVars
  then HFail
  else HNothing
  where 
    matchVars :: [(String,LNTerm)] -> [(String,LNTerm)] -> [(String,String)]
    matchVars [] _ = []
    matchVars _ [] = []
    matchVars (v:vs) vs2 =
      let matches = filter (\vv2 -> (snd v) == (snd vv2)) vs2 in
      if (isVar $ snd v) && (not $ null matches)
      then (map (\(m,_) -> (fst v, m)) matches) ++ matchVars vs vs2
      else matchVars vs vs2

failureTwoHomomorphicRule :: HomomorphicRule
failureTwoHomomorphicRule eq _ _ = let 
  n = (length $ eRep $ eqRHS eq) - 1 
  eRepsLHS = eRepsTerms $ pRep $ eqLHS eq
  in if any (\e -> (not $ isVar $ head $ e) && (length e < n + 1)) eRepsLHS
  then HFail
  else HNothing

parsingHomomorphicRule :: HomomorphicRule
parsingHomomorphicRule eq _ _ = let
  eRepsLHS = eRepsTerms $ pRep $ eqLHS eq
  strRepsLHS = eRepsString $ pRep $ eqLHS eq
  newERepsLHS = map init eRepsLHS
  eRepRHS = eRep $ eqRHS eq
  newLHS = toLNPETerm $ fromPRepresentation $ PRep strRepsLHS newERepsLHS
  newRHS = toLNPETerm $ fromERepresentation $ init eRepRHS
  allKms = map toLNPETerm $ [last eRepRHS] ++ (map last eRepsLHS)
  in if all (\t -> length t >= 2) (eRepsLHS ++ [eRepRHS])
  then HEqs $ [Equal newLHS newRHS] ++ (getAllCombinations allKms) 
  else HNothing
  where
    getAllCombinations :: [LNPETerm] -> [Equal LNPETerm]
    getAllCombinations [] = []
    getAllCombinations (x:xs) = pairCombinations x xs ++ getAllCombinations xs
    pairCombinations _ [] = []
    pairCombinations x (y:ys) = [Equal x y] ++ pairCombinations x ys

-- | Takes a sort and equation and returns a substitution for terms so that they unify or an empty list 
-- if it is not possible to unify the terms
-- from SubstVFresh.hs: LNSubstVFresh = SubstVFresh { svMap :: Map LVar LNTerm }
unifyHomomorphicLTermFactored :: (Name -> LSort) -> [Equal LNTerm] -> [LNSubst]
unifyHomomorphicLTermFactored sortOf eqs =
  toSubst $ applyHomomorphicRules sortOf allHomomorphicRules (tpre eqsN)
  where 
    eqsN = normHomomorphicEqs eqs
    toSubst [] = 
      if and $ map (\eq -> (eqLHS eq) == (eqRHS eq)) eqsN
      then [emptySubst]
      else []
    toSubst eqsSubst = case toHomomorphicSolvedForm eqsSubst of
      Just normEqsSubst -> [Subst $ M.fromList $ map (\eq -> (getLeftVar eq, eqRHS eq)) normEqsSubst]
      Nothing -> []
    tpre eqsLN = 
      map (fmap toLNPETerm) eqsLN
    getLeftVar e = case getVar $ eqLHS e of
      Just v -> v
      Nothing -> (LVar "VARNOTFOUND" LSortFresh 0)

-- | Applies all homomorphic rules given en block, i.e., 
-- it applies the first rule always first after each change
applyHomomorphicRules :: (Name -> LSort) -> [HomomorphicRule] -> [Equal LNPETerm] -> [Equal LNPETerm]
applyHomomorphicRules _ [] eqs = eqs -- no more rules to apply 
applyHomomorphicRules sortOf (rule:rules) eqs =
  case applyHomomorphicRule rule sortOf eqs [] of
    Just newEqs -> applyHomomorphicRules sortOf allHomomorphicRules newEqs
    Nothing     -> applyHomomorphicRules sortOf rules eqs

-- | Applies the homomorphic rule to the first term possible in equation list or returns Nothing 
-- if the rule is not applicable to any terms
applyHomomorphicRule :: HomomorphicRule -> (Name -> LSort) -> [Equal LNPETerm] -> [Equal LNPETerm] -> Maybe [Equal LNPETerm]
applyHomomorphicRule _ _ [] _ = Nothing
applyHomomorphicRule rule sortOf (equation:equations) passedEqs =
  case rule equation sortOf (passedEqs ++ equations) of
    HEqs newEqs ->            Just (passedEqs ++ newEqs ++ equations)
    HSubstEqs subst newEqs -> Just $ (map (applySubstitution subst) (passedEqs ++ equations)) ++ newEqs
    HNothing ->               applyHomomorphicRule rule sortOf equations (equation:passedEqs)
    HFail ->                  Just []
  where
    applySubstitution subst eq = Equal 
      (toLNPETerm $ applyVTerm subst $ lnTerm $ eqLHS eq) 
      (toLNPETerm $ applyVTerm subst $ lnTerm $ eqRHS eq)

-- | Normalizes equations to Homomorphic Solved Form
-- Returns Nothing if equations not possible to put in Homomorphic Solved Form
toHomomorphicSolvedForm :: [Equal LNPETerm] -> Maybe [Equal LNTerm]
toHomomorphicSolvedForm eqs = let
  eqsLN = map (\eq -> (Equal (lnTerm $ eqLHS eq) (lnTerm $ eqRHS eq))) eqs
  varLeftEqs = map moveVarLeft eqsLN
  vLEqsNoDups = removeDuplicates varLeftEqs
  doubleVarEqs = filter doubleVarEq vLEqsNoDups
  singleVarEqs = filter (not . doubleVarEq) vLEqsNoDups
  sLeftVars = map eqLHS singleVarEqs
  sRightTerms = map eqRHS singleVarEqs
  orderedDVarEqs = orderDoubleVarEqs doubleVarEqs (sLeftVars ++ sRightTerms)
  dLeftVars = map eqLHS orderedDVarEqs
  dRightTerms = map eqRHS orderedDVarEqs
  leftVars = sLeftVars ++ dLeftVars
  rightTerms = sRightTerms ++ dRightTerms
  in if (allLeftVarsUnique leftVars) && (allLeftVarsNotRight leftVars rightTerms)
  then Just (singleVarEqs ++ orderedDVarEqs)
  else Nothing
  where
    moveVarLeft :: Equal LNTerm -> Equal LNTerm
    moveVarLeft e =
      case (viewTerm $ eqLHS e, viewTerm $ eqRHS e) of 
        (FApp _ _,    Lit (Var _)) -> Equal (eqRHS e) (eqLHS e)
        (Lit (Con _), Lit (Var _)) -> Equal (eqRHS e) (eqLHS e)
        (_, _)                     -> Equal (eqLHS e) (eqRHS e)
    removeDuplicates :: [Equal LNTerm] -> [Equal LNTerm]
    removeDuplicates [] = []
    removeDuplicates (e:es) = if any (\e2 -> 
         ((eqLHS e) == (eqLHS e2) && (eqRHS e) == (eqRHS e2))
      || ((eqLHS e) == (eqRHS e2) && (eqRHS e) == (eqLHS e2))) es
      then es
      else e:(removeDuplicates es)
    doubleVarEq :: Equal LNTerm -> Bool
    doubleVarEq e = 
      case (viewTerm $ eqLHS e, viewTerm $ eqRHS e) of
        (Lit (Var _), Lit (Var _)) -> True
        (_, _)                     -> False
    allLeftVarsUnique :: [LNTerm] -> Bool
    allLeftVarsUnique [] = True
    allLeftVarsUnique (l:ls) = (varNotPartOfTerms l ls) && (allLeftVarsUnique ls)
    allLeftVarsNotRight :: [LNTerm] -> [LNTerm] -> Bool
    allLeftVarsNotRight [] _ = True
    allLeftVarsNotRight (l:ls) rs = (varNotPartOfTerms l rs) && (allLeftVarsNotRight ls rs)
    orderDoubleVarEqs :: [Equal LNTerm] -> [LNTerm] -> [Equal LNTerm]
    orderDoubleVarEqs [] _ = []
    orderDoubleVarEqs (e:es) rs =
      case (varNotPartOfTerms (eqLHS e) (rs ++ (eqsToTerms es)), varNotPartOfTerms (eqRHS e) (rs ++ (eqsToTerms es))) of
        (True, _) -> e : (orderDoubleVarEqs es (rs ++ [(eqLHS e), (eqRHS e)]))
        (_, True) -> (Equal (eqRHS e) (eqLHS e)) : (orderDoubleVarEqs es (rs ++ [(eqLHS e), (eqRHS e)]))
        (_,_) -> e : (orderDoubleVarEqs es (rs ++ [(eqLHS e), (eqRHS e)]))
    eqsToTerms :: [Equal LNTerm] -> [LNTerm]
    eqsToTerms [] = []
    eqsToTerms (e:es) = [eqLHS e, eqRHS e] ++ (eqsToTerms es)
    varNotPartOfTerms :: LNTerm -> [LNTerm] -> Bool
    varNotPartOfTerms _ [] = True
    varNotPartOfTerms l (r:rs) = 
      case (viewTerm l) of
        (Lit (Var _)) -> (varNotPartOfTerm l r) && (varNotPartOfTerms l rs)
        (_)           -> False
    varNotPartOfTerm :: LNTerm -> LNTerm -> Bool
    varNotPartOfTerm l r =
      case (viewTerm r) of
        (FApp _ args) -> all (varNotPartOfTerm l) args
        (Lit (Var _)) -> l /= r
        (Lit (Con _)) -> True

-- | @unifyHomomorphicLNTerm eqs@ returns a set of unifiers for @eqs@ modulo EpsilonH.
--
-- LNTerm = Term (Lit (Con Name | Var LVar) | FApp FunSym [Term Lit ((Con Name | Var LVar))])
-- use viewTerm to use "case of" term
-- Equal LNTerm = Equal { eqLHS :: LNTerm, eqRHS :: LNTerm }
--
-- sortOfName :: Name -> LSort
-- data LSort = LSortPub | LSortFresh | LSortMsg | LSortNode -- Nodes are for dependency graphs
unifyHomomorphicLNTerm :: [Equal LNTerm] -> [LNSubst]
unifyHomomorphicLNTerm eqs = unifyHomomorphicLTermFactored sortOfName eqs

normHomomorphicEqs :: [Equal LNTerm] -> [Equal LNTerm]
normHomomorphicEqs eqs = map (\e -> Equal (normHomomorphic $ eqLHS e) (normHomomorphic $ eqRHS e)) eqs

-- | @normHomomorphic t@ normalizes the term @t@ if the top function is the homomorphic encryption
normHomomorphic :: LNTerm -> LNTerm
normHomomorphic t = case viewTerm t of
  (FApp sym [FAPP (NoEq sym2) [t1, t2], t3]) -> 
    if (isHenc sym) && (isPair (FAPP (NoEq sym2) [t1, t2]))
    then fAppPair (FAPP (getHencSym) [t1, t3], FAPP (getHencSym) [t2, t3])
    else FAPP sym (map normHomomorphic [FAPP (NoEq sym2) [t1, t2], t3])
  (FApp sym args) -> FAPP sym (map normHomomorphic args)
  (_) -> t