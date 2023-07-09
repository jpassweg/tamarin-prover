{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- AC unification based on maude and free unification.
module Term.Unification (
  -- * Unification modulo AC
    unifyLTerm
  , unifyLNTerm
  , unifiableLNTerms

  , unifyLTermFactored
  , unifyLNTermFactored

  -- * Unification without AC
  , unifyLTermNoAC
  , unifyLNTermNoAC
  , unifiableLNTermsNoAC

  , unifyLTermFactoredNoAC
  , unifyLNTermFactoredNoAC

  -- * Unification modulo EpsilonH for Homomorphic Encryption
  , unifyHomomorphicLNTerm

  -- * matching modulo AC
  -- ** Constructing matching problems
  , matchLVar

  -- ** Solving matching problems
  , solveMatchLTerm
  , solveMatchLNTerm

  -- * Handles to a Maude process
  , MaudeHandle
  , WithMaude
  , startMaude
  , getMaudeStats
  , mhMaudeSig
  , mhFilePath

  -- * Maude signatures
  , MaudeSig
  , enableDH
  , enableBP
  , enableMSet
  , enableXor
  , enableDiff
  , minimalMaudeSig
  , enableDiffMaudeSig
  , dhMaudeSig
  , bpMaudeSig
  , xorMaudeSig
  , msetMaudeSig
  , pairMaudeSig
  , symEncMaudeSig
  , asymEncMaudeSig
  , signatureMaudeSig
  , pairDestMaudeSig
  , symEncDestMaudeSig
  , asymEncDestMaudeSig
  , signatureDestMaudeSig  
  , locationReportMaudeSig
  , revealSignatureMaudeSig
  , hashMaudeSig
  , rrulesForMaudeSig
  , stFunSyms
  , funSyms
  , stRules
  , irreducibleFunSyms
  , reducibleFunSyms
  , noEqFunSyms
  , addFunSym
  , addCtxtStRule

  -- * Convenience exports
  , module Term.Substitution
  , module Term.Rewriting.Definitions
) where

-- import           Control.Applicative
import           Control.Monad.RWS
import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.Map as M
import           Data.Map (Map)

import           System.IO.Unsafe (unsafePerformIO)


import           Term.Rewriting.Definitions
import           Term.Substitution
import           Term.Term.FunctionSymbols
import           Term.Builtin.Signature
import qualified Term.Maude.Process as UM
import           Term.Maude.Process
                   (MaudeHandle, WithMaude, startMaude, getMaudeStats, mhMaudeSig, mhFilePath)
import           Term.Maude.Signature
import           Debug.Trace.Ignore

-- Unification modulo AC
----------------------------------------------------------------------

-- | @unifyLTerm sortOf eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLTermFactored :: (IsConst c)
                   => (c -> LSort)
                   -> [Equal (LTerm c)]
                   -> WithMaude (LSubst c, [SubstVFresh c LVar])
unifyLTermFactored sortOf eqs = reader $ \h -> (\res -> trace (unlines $ ["unifyLTerm: "++ show eqs, "result = "++  show res]) res) $ do
    solve h $ execRWST unif sortOf M.empty
  where
    unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
    solve _ Nothing         = (emptySubst, [])
    solve _ (Just (m, []))  = (substFromMap m, [emptySubstVFresh])
    solve h (Just (m, leqs)) =
        (subst, unsafePerformIO (UM.unifyViaMaude h sortOf $
                                     map (applyVTerm subst <$>) leqs))
      where subst = substFromMap m


-- | @unifyLTerm sortOf eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLNTermFactored :: [Equal LNTerm]
                    -> WithMaude (LNSubst, [SubstVFresh Name LVar])
unifyLNTermFactored = unifyLTermFactored sortOfName

-- | @unifyLNTerm eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLTerm :: (IsConst c)
           => (c -> LSort)
           -> [Equal (LTerm c)]
           -> WithMaude [SubstVFresh c LVar]
unifyLTerm sortOf eqs = flattenUnif <$> unifyLTermFactored sortOf eqs


-- | @unifyLNTerm eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLNTerm :: [Equal LNTerm] -> WithMaude [SubstVFresh Name LVar]
unifyLNTerm = unifyLTerm sortOfName

-- | 'True' iff the terms are unifiable.
unifiableLNTerms :: LNTerm -> LNTerm -> WithMaude Bool
unifiableLNTerms t1 t2 = (not . null) <$> unifyLNTerm [Equal t1 t2]

-- | Flatten a factored substitution to a list of substitutions.
flattenUnif :: IsConst c => (LSubst c, [LSubstVFresh c]) -> [LSubstVFresh c]
flattenUnif (subst, substs) =
    (\res -> trace (show ("flattenUnif",subst, substs,res )) res) $ map (`composeVFresh` subst) substs

-- Unification without AC
----------------------------------------------------------------------

-- | @unifyLTermFactoredAC sortOf eqs@ returns a complete set of unifiers for @eqs@ for terms without AC symbols.
unifyLTermFactoredNoAC :: (IsConst c)
                   => (c -> LSort)
                   -> [Equal (LTerm c)]
                   -> [(SubstVFresh c LVar)]
unifyLTermFactoredNoAC sortOf eqs = (\res -> trace (unlines $ ["unifyLTermFactoredNoAC: "++ show eqs, "result = "++  show res]) res) $ do
    solve $ execRWST unif sortOf M.empty
  where
    unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
    solve Nothing         = []
    solve (Just (m, []))  = [freeToFreshRaw (substFromMap m)]
    -- if delayed AC unifications occur, we fail
    solve (Just _     )   = error "No AC unification, but AC symbol found."


-- | @unifyLNTermFactoredNoAC sortOf eqs@ returns a complete set of unifiers for @eqs@ for terms without AC symbols.
unifyLNTermFactoredNoAC :: [Equal LNTerm]
                    -> [(SubstVFresh Name LVar)]
unifyLNTermFactoredNoAC = unifyLTermFactoredNoAC sortOfName

-- | @unifyLNTermNoAC eqs@ returns a complete set of unifiers for @eqs@  for terms without AC symbols.
unifyLTermNoAC :: (IsConst c)
           => (c -> LSort)
           -> [Equal (LTerm c)]
           -> [SubstVFresh c LVar]
unifyLTermNoAC sortOf eqs = unifyLTermFactoredNoAC sortOf eqs

-- | @unifyLNTermNoAC eqs@ returns a complete set of unifiers for @eqs@  for terms without AC symbols.
unifyLNTermNoAC :: [Equal LNTerm] -> [SubstVFresh Name LVar]
unifyLNTermNoAC = unifyLTermNoAC sortOfName

-- | 'True' iff the terms are unifiable.
unifiableLNTermsNoAC :: LNTerm -> LNTerm -> Bool
unifiableLNTermsNoAC t1 t2 = not $ null $ unifyLNTermNoAC [Equal t1 t2]

-- Unification modulo EpsilonH
----------------------------------------------------------------------

-- | Return type for a HomomorphicRule
data HomomorphicRuleReturn = HEqs [Equal LNPETerm] 
  | HSubstEqs LNSubst [Equal LNPETerm] 
  | HNothing
  | HFail

-- | Type for rules applied to equations for unification modulo EpsilonH
type HomomorphicRule = Equal LNPETerm -> (Name -> LSort) -> [Equal LNPETerm] -> HomomorphicRuleReturn

-- | All homomorphic rules in order of application
allHomomorphicRules :: [HomomorphicRule]
allHomomorphicRules = (\rules -> rules ++ map switchedWrapperHomomorphicRule rules)
  [ failureOneHomomorphicRule -- failure rules first
  , failureTwoHomomorphicRule
  , occurCheckHomomorphicRule
  , clashHomomorphicRule      -- then Homomorphic patterns
  , shapingHomomorphicRule    -- shaping best before parsing
  , parsingHomomorphicRule
  -- varSub en block with Homorphic patterns
  , variableSubstitutionHomomorphicRule
  -- then other rules
  , trivialHomomorphicRule
  , stdDecompositionHomomorphicRule]

switchedWrapperHomomorphicRule :: HomomorphicRule -> HomomorphicRule
switchedWrapperHomomorphicRule rule eq sortOf eqs =
  rule (Equal (eqRHS eq) (eqLHS eq)) sortOf eqs

trivialHomomorphicRule :: HomomorphicRule
trivialHomomorphicRule eq sortOf eqs = if 
    (uncurry eqSyntatic) $ (\e -> (fromLNPETerm $ eqLHS e, fromLNPETerm $ eqRHS e)) eq
  then HEqs []
  else HNothing

stdDecompositionHomomorphicRule :: HomomorphicRule
stdDecompositionHomomorphicRule eq sortOf eqs =
  case (viewTerm $ fromLNPETerm $ eqLHS eq, viewTerm $ fromLNPETerm $ eqRHS eq) of
    -- TODO finish implementation, also have a look at viewTerm2
    (FApp (NoEq lfsym) largs, FApp (NoEq rfsym) rargs)  -> 
      addArgs (lfsym == rfsym && length largs == length rargs) largs rargs 
    (FApp List largs, FApp List rargs)                  -> 
      addArgs (length largs == length rargs) largs rargs
    (FApp (AC lacsym) largs, FApp (AC racsym) rargs)    -> 
      addArgs (lacsym == racsym && length largs == length rargs) largs rargs
    (FApp (C lcsym) largs, FApp (C rcsym) rargs)        -> 
      addArgs (lcsym == rcsym && length largs == length rargs) largs rargs
    (_,_)                                               -> HNothing
  where
    addArgs b las ras = if b
      then HEqs $ map (\(a,b) -> Equal (toLNPETerm a) (toLNPETerm b)) $ zip las ras
      else HNothing

variableSubstitutionHomomorphicRule :: HomomorphicRule
variableSubstitutionHomomorphicRule eq sortOf eqs =
  case (viewTerm $ fromLNPETerm $ eqLHS eq) of
    (Lit (Var nameLHS)) -> if 
        (not $ occursVTerm nameLHS (fromLNPETerm $ eqRHS eq)) 
        && (occursEqs nameLHS eqs) 
      then HSubstEqs 
        (Subst $ M.fromList [(nameLHS, fromLNPETerm $ eqRHS eq)]) [eq]
      else HNothing
    _ -> HNothing
  where
    occursEqs n es = 
      any (\(Equal a b) -> (occursVTerm n $ fromLNPETerm a) 
      || (occursVTerm n $ fromLNPETerm b)) es

-- Find pairSym in Term.Term.FunctionSymbols 
-- and sencSym in Term.Builtin.Signature
clashHomomorphicRule :: HomomorphicRule
clashHomomorphicRule eq sortOf eqs = 
  case (viewTerm $ fromLNPETerm $ eqLHS eq, viewTerm $ fromLNPETerm $ eqRHS eq) of
    (FApp (NoEq oleft) _, FApp (NoEq oright) _) -> if 
           (oleft == pairSym && oright == sencSym) 
        || (oleft == sencSym && oright == pairSym) 
        || oleft == oright
      then HNothing
      else HFail
    _ -> HNothing

occurCheckHomomorphicRule :: HomomorphicRule
occurCheckHomomorphicRule eq sortOf eqs = 
  case getVar $ fromLNPETerm $ eqLHS eq of
    Just v  -> if 
        (not $ eqSyntatic (fromLNPETerm $ eqLHS eq) (fromLNPETerm $ eqRHS eq))
        && (occursVTerm v (fromLNPETerm $ eqRHS eq))
      then HFail
      else HNothing
    Nothing -> HNothing

shapingHomomorphicRule :: HomomorphicRule
shapingHomomorphicRule eq sortOf eqs = let
  eRepsLHS = terms $ pRep $ eqLHS eq
  strLHS = bitString $ pRep $ eqLHS eq
  eRepRHS = eRep $ eqRHS eq
  pl = (length $ eRepsLHS) 
  n = (length $ eRepRHS) - 1
  in if pl >= 2 && n >= 2
  then case findQualifyingETerm eRepsLHS 0 of
    Just qualifyingIndex -> let 
      qualifyingELhs = eRepsLHS !! qualifyingIndex
      m = n + 1 - (length qualifyingELhs)
      xnew = varTerm $ LVar "fxShapingHomomorphic" LSortFresh $ (getFreshVarCounter ([eq] ++ eqs) 0) + 1
      x = toLNPETerm $ head qualifyingELhs
      lhs1NewETerm = ([xnew] ++ (take (m-1) (tail eRepRHS)) ++ (tail qualifyingELhs))
      lhs1NewPTerm = let (ys,zs) = splitAt qualifyingIndex eRepsLHS in
        PRep strLHS (ys ++ [lhs1NewETerm] ++ (tail zs))
      rhs2ETerm = [xnew] ++ (take (m-1) (tail eRepRHS))
      lhs1 = toLNPETerm $ fromPRepresentation lhs1NewPTerm
      rhs1 = eqRHS eq
      lhs2 = x
      rhs2 = toLNPETerm $ fromERepresentation rhs2ETerm
      in 
        HEqs [Equal lhs1 rhs1, Equal lhs2 rhs2] 
    Nothing -> HNothing
  else HNothing
  where
    findQualifyingETerm :: [[LNTerm]] -> Int -> Maybe Int
    findQualifyingETerm [] _ = Nothing
    findQualifyingETerm (e:es) ind =
      if length e >= 2
      then Just ind
      else findQualifyingETerm es (ind+1)
    getFreshVarCounter [] n = n
    getFreshVarCounter (q:qs) n = getFreshVarCounter qs $ max n 
      $ lvarIdx
      $ foldr (\lv1 lv2 -> if lvarIdx lv1 >= lvarIdx lv2 then lv1 else lv2) 
      (LVar "fxShapingHomomorphic" LSortFresh 0)
      $ filter (\lv -> lvarName lv == "fxShapingHomomorphic")
      $ (frees $ fromLNPETerm $ eqLHS q) ++ (frees $ fromLNPETerm $ eqRHS q)

failureOneHomomorphicRule :: HomomorphicRule
failureOneHomomorphicRule eq sortOf eqs = let
    t1 = positionsWithTerms (fromLNPETerm $ eqLHS eq) ""
    t2 = positionsWithTerms (fromLNPETerm $ eqRHS eq) ""
    t1NonKey = filter (\(p,tt) -> all (\bc -> bc == '1') (ePosition p tt)) t1
    t2NonKey = filter (\(p,tt) -> all (\bc -> bc == '1') (ePosition p tt)) t2
    matchedVars = matchVars t1NonKey t2NonKey
  in
  if any (uncurry4 positionsIncompatible) matchedVars
  then HFail
  else HNothing
  where 
    matchVars :: [(String,LNTerm)] -> [(String,LNTerm)] -> [(String,LNTerm,String,LNTerm)]
    matchVars [] _ = []
    matchVars _ [] = []
    matchVars (v:vs) vs2 =
      let matches = filter (\v2 -> eqSyntatic (snd v) (snd v2)) vs2 in
      if (isVar $ snd v) && (not $ null matches)
      then (map (\(m1,m2) -> (fst v, snd v, m1, m2)) matches) ++ matchVars vs vs2
      else matchVars vs vs2
    uncurry4 f (a,b,c,d) = f a b c d

failureTwoHomomorphicRule :: HomomorphicRule
failureTwoHomomorphicRule eq sortOf eqs = let 
  n = (length $ eRep $ eqRHS eq) - 1 
  eRepsLHS = terms $ pRep $ eqLHS eq
  in if any (\e -> (not $ isVar $ head $ e) && (length e < n + 1)) eRepsLHS
  then HFail
  else HNothing

parsingHomomorphicRule :: HomomorphicRule
parsingHomomorphicRule eq sortOf eqs = let
  eRepsLHS = terms $ pRep $ eqLHS eq
  strRepsLHS = bitString $ pRep $ eqLHS eq
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
unifyHomomorphicLTermFactored :: (Name -> LSort) -> [Equal LNTerm] -> [LNSubstVFresh]
unifyHomomorphicLTermFactored sortOf eqs = 
  toSubst $ applyHomomorphicRules sortOf allHomomorphicRules (tpre eqs)
  where 
    toSubst [] = 
      if and 
        $ map (uncurry eqSyntatic) 
        $ map (\eq -> (eqLHS eq, eqRHS eq)) eqs
      then [emptySubstVFresh]
      else []
    toSubst eqsSubst = 
      let normEqsSubst = map normalizeEq eqsSubst in
      if inHomomorphicSolvedForm normEqsSubst
      then [SubstVFresh 
        $ M.fromList 
        $ map (\eq -> 
          (liftMaybe $ getVar $ fromLNPETerm $ eqLHS eq, 
          fromLNPETerm $ eqRHS eq)
        ) 
        normEqsSubst]
      else []
    tpre eqsLN = 
      map (\eq -> Equal 
      (toLNPETerm $ eqLHS eq) 
      (toLNPETerm $ eqRHS eq)) eqsLN
    normalizeEq eq =
      let 
      t1 = eqLHS eq
      t2 = eqRHS eq
      v1 = viewTerm $ fromLNPETerm t1
      v2 = viewTerm $ fromLNPETerm t2
      in case (v1,v2) of
        (FApp _ _, Lit (Var _)) -> Equal t2 t1
        (Lit (Con _), Lit (Var _)) -> Equal t2 t1
        (_, _) -> Equal t1 t2
    liftMaybe jv = let Just v = jv in v 

-- | Applies all homomorphic rules given en block, i.e., 
-- it applies the first rule always first after each change
applyHomomorphicRules :: (Name -> LSort) -> [HomomorphicRule] -> [Equal LNPETerm] -> [Equal LNPETerm]
applyHomomorphicRules sortOf [] eqs = -- no more rules to apply 
  if inHomomorphicSolvedForm eqs
    then eqs
    else []
applyHomomorphicRules sortOf (rule:rules) eqs = 
  if inHomomorphicSolvedForm eqs
    then eqs
    else case applyHomomorphicRule rule sortOf eqs [] of
      Just newEqs -> applyHomomorphicRules sortOf allHomomorphicRules newEqs
      Nothing     -> applyHomomorphicRules sortOf rules eqs

-- | Applies the homomorphic rule to the first term possible in equation list or returns Nothing 
-- if the rule is not applicable to any terms
applyHomomorphicRule :: HomomorphicRule -> (Name -> LSort) -> [Equal LNPETerm] -> [Equal LNPETerm] -> Maybe [Equal LNPETerm]
applyHomomorphicRule _ sortOf [] _ = Nothing
applyHomomorphicRule rule sortOf (equation:equations) passedEqs =
  case rule equation sortOf (passedEqs ++ equations) of
    HEqs newEqs ->            Just (passedEqs ++ newEqs ++ equations)
    HSubstEqs subst newEqs -> Just $ (map (applySubstitution subst) (passedEqs ++ equations)) ++ newEqs
    HNothing ->               applyHomomorphicRule rule sortOf equations (equation:passedEqs)
    HFail ->                  Just []
  where
    applySubstitution subst eq = 
      Equal 
      (toLNPETerm $ applyVTerm subst $ fromLNPETerm $ eqLHS eq) 
      (toLNPETerm $ applyVTerm subst $ fromLNPETerm $ eqRHS eq)

-- | Checks if equations are in the solved form according to the homomorphic theory
inHomomorphicSolvedForm :: [Equal LNPETerm] -> Bool
inHomomorphicSolvedForm eqs = all (\eq -> case viewTerm $ fromLNPETerm $ eqLHS eq of
  (Lit (Var _)) -> True
  _ -> False) eqs

-- | @unifyHomomorphicLNTerm eqs@ returns a set of unifiers for @eqs@ modulo EpsilonH.
--
-- LNTerm = Term (Lit (Con Name | Var LVar) | FApp FunSym [Term Lit ((Con Name | Var LVar))])
-- use viewTerm to use "case of" term
-- Equal LNTerm = Equal { eqLHS :: LNTerm, eqRHS :: LNTerm }
--
-- sortOfName :: Name -> LSort
-- data LSort = LSortPub | LSortFresh | LSortMsg | LSortNode -- Nodes are for dependency graphs
unifyHomomorphicLNTerm :: [Equal LNTerm] -> [LNSubstVFresh]
unifyHomomorphicLNTerm eqs = unifyHomomorphicLTermFactored sortOfName eqs

-- Matching modulo AC
----------------------------------------------------------------------

-- | Match an 'LVar' term to an 'LVar' pattern.
matchLVar :: LVar -> LVar -> Match (LTerm c)
matchLVar t p = varTerm t `matchWith` varTerm p

-- | @solveMatchLNTerm sortOf eqs@ returns a complete set of matchers for
-- @eqs@ modulo AC.
solveMatchLTerm :: (IsConst c)
           => (c -> LSort)
           -> Match (LTerm c)
           -> WithMaude [Subst c LVar]
solveMatchLTerm sortOf matchProblem =
    case flattenMatch matchProblem of
      Nothing -> pure []
      Just ms -> reader $ matchTerms ms
  where
    trace' res = trace
      (unlines $ ["matchLTerm: "++ show matchProblem, "result = "++  show res])
      res

    matchTerms ms hnd =
        trace' $ case runState (runExceptT match) M.empty of
          (Left NoMatcher, _)  -> []
          (Left ACProblem, _)  ->
              unsafePerformIO (UM.matchViaMaude hnd sortOf matchProblem)
          (Right (), mappings) -> [substFromMap mappings]
      where
        match = forM_ ms $ \(t, p) -> matchRaw sortOf t p


-- | @solveMatchLNTerm eqs@ returns a complete set of matchers for @eqs@
-- modulo AC.
solveMatchLNTerm :: Match LNTerm -> WithMaude [Subst Name LVar]
solveMatchLNTerm = solveMatchLTerm sortOfName

-- Free unification with lazy AC-equation solving.
--------------------------------------------------------------------

type UnifyRaw c = RWST (c -> LSort) [Equal (LTerm c)] (Map LVar (VTerm c LVar)) Maybe

-- | Unify two 'LTerm's with delayed AC-unification.
unifyRaw :: IsConst c => LTerm c -> LTerm c -> UnifyRaw c ()
unifyRaw l0 r0 = do
    mappings <- get
    sortOf <- ask
    l <- gets ((`applyVTerm` l0) . substFromMap)
    r <- gets ((`applyVTerm` r0) . substFromMap)
    guard (trace (show ("unifyRaw", mappings, l ,r)) True)
    case (viewTerm l, viewTerm r) of
       (Lit (Var vl), Lit (Var vr))
         | vl == vr  -> return ()
         | otherwise -> case (lvarSort vl, lvarSort vr) of
             (sl, sr) | sl == sr                 -> if vl < vr then elim vr l
                                                    else elim vl r
             _        | sortGeqLTerm sortOf vl r -> elim vl r
             -- If unification can succeed here, then it must work by
             -- elimating the right-hand variable with the left-hand side.
             _                                   -> elim vr l

       (Lit (Var vl),  _            ) -> elim vl r
       (_,             Lit (Var vr) ) -> elim vr l
       (Lit (Con cl),  Lit (Con cr) ) -> guard (cl == cr)
       (FApp (NoEq lfsym) largs, FApp (NoEq rfsym) rargs) ->
           guard (lfsym == rfsym && length largs == length rargs)
           >> sequence_ (zipWith unifyRaw largs rargs)
       (FApp List largs, FApp List rargs) ->
           guard (length largs == length rargs)
           >> sequence_ (zipWith unifyRaw largs rargs)
       -- NOTE: We assume here that terms of the form mult(t) never occur.
       (FApp (AC lacsym) _, FApp (AC racsym) _) ->
           guard (lacsym == racsym) >> tell [Equal l r]  -- delay unification

       (FApp (C lsym) largs, FApp (C rsym) rargs) ->
           guard (lsym == rsym && length largs == length rargs)
           >> tell [Equal l r]  -- delay unification

       -- all unifiable pairs of term constructors have been enumerated
       _                      -> mzero -- no unifier
  where
    elim v t
      | v `occurs` t = mzero -- no unifier
      | otherwise    = do
          sortOf <- ask
          guard  (sortGeqLTerm sortOf v t)
          modify (M.insert v t . M.map (applyVTerm (substFromList [(v,t)])))


data MatchFailure = NoMatcher | ACProblem

instance Semigroup MatchFailure where
  _ <> _ = NoMatcher

instance Monoid MatchFailure where
  mempty = NoMatcher

-- | Ensure that the computed substitution @sigma@ satisfies
-- @t ==_AC apply sigma p@ after the delayed equations are solved.
matchRaw :: IsConst c
         => (c -> LSort)
         -> LTerm c -- ^ Term @t@
         -> LTerm c -- ^ Pattern @p@.
         -> ExceptT MatchFailure (State (Map LVar (VTerm c LVar))) ()
matchRaw sortOf t p = do
    mappings <- get
    guard (trace (show (mappings,t,p)) True)
    case (viewTerm t, viewTerm p) of
      (_, Lit (Var vp)) ->
          case M.lookup vp mappings of
              Nothing             -> do
                unless (sortGeqLTerm sortOf vp t) $
                    throwError NoMatcher
                modify (M.insert vp t)
              Just tp | t == tp  -> return ()
                      | otherwise -> throwError NoMatcher

      (Lit (Con ct),  Lit (Con cp)) -> guard (ct == cp)
      (FApp (NoEq tfsym) targs, FApp (NoEq pfsym) pargs) ->
           guard (tfsym == pfsym && length targs == length pargs)
           >> sequence_ (zipWith (matchRaw sortOf) targs pargs)
      (FApp List targs, FApp List pargs) ->
           guard (length targs == length pargs)
           >> sequence_ (zipWith (matchRaw sortOf) targs pargs)
      (FApp (AC _) _, FApp (AC _) _) -> throwError ACProblem
      (FApp (C _) _, FApp (C _) _) -> throwError ACProblem

      -- all matchable pairs of term constructors have been enumerated
      _                      -> throwError NoMatcher


-- | @sortGreaterEq v t@ returns @True@ if the sort ensures that the sort of @v@ is greater or equal to
--   the sort of @t@.
sortGeqLTerm :: IsConst c => (c -> LSort) -> LVar -> LTerm c -> Bool
sortGeqLTerm st v t = do
    case (lvarSort v, sortOfLTerm st t) of
        (s1, s2) | s1 == s2     -> True
        -- Node is incomparable to all other sorts, invalid input
        (LSortNode,  _        ) -> errNodeSort
        (_,          LSortNode) -> errNodeSort
        (s1, s2)                -> sortCompare s1 s2 `elem` [Just EQ, Just GT]
  where
    errNodeSort = error $
        "sortGeqLTerm: node sort misuse " ++ show v ++ " -> " ++ show t
