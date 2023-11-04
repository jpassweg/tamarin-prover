{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- AC unification based on maude and free unification.
module Term.Unification (
  unifyUnionDisjointTheories

  -- * Unification modulo AC
  , unifyLTerm
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
  , enableNat
  , enableXor
  , enableHom
  , enableDiff
  , minimalMaudeSig
  , enableDiffMaudeSig
  , dhMaudeSig
  , homMaudeSig
  , natMaudeSig
  , bpMaudeSig
  , xorMaudeSig
  , msetMaudeSig
  , pairMaudeSig
  , symEncMaudeSig
  , asymEncMaudeSig
  , signatureMaudeSig
  , pairDestMaudeSig
  , homPairDestMaudeSig
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
import           Data.Maybe (maybeToList, mapMaybe)
import           Data.List (permutations)

import           System.IO.Unsafe (unsafePerformIO)


import           Term.Term.FunctionSymbols
import           Term.Rewriting.Definitions
import           Term.Substitution
import qualified Term.Maude.Process as UM
import           Term.Maude.Process
                   (MaudeHandle, WithMaude, startMaude, getMaudeStats, mhMaudeSig, mhFilePath)
import           Term.Maude.Signature
import           Term.Homomorphism.Unification
import           Debug.Trace.Ignore
import Control.Arrow (Arrow(second))

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
    solve h subst = if enableHom $ mhMaudeSig h
      then case subst of
        Nothing        -> (emptySubst, [])
        Just (m, [])   -> (substFromMap m, [emptySubstVFresh])
        Just (m, leqs) -> (substFromMap m, unifyHomomorphicLTermWrapper sortOf leqs)
      else case subst of
        Nothing        -> (emptySubst, [])
        Just (m, [])   -> (substFromMap m, [emptySubstVFresh])
        Just (m, leqs) -> (substFromMap m, unsafePerformIO (UM.unifyViaMaude h sortOf $ map (applyVTerm (substFromMap m) <$>) leqs))

-- TODO: removed map (applyVTerm (substFromMap m) <$>)
-- unifyRaw return must be applied to eqs before adding them here
unifyUnionDisjointTheories :: IsConst c => (c -> LSort) -> MaudeHandle -> [Equal (LTerm c)] -> [LSubstVFresh c]
unifyUnionDisjointTheories sortOf mhnd eqs = let
  allVars = foldVars $ eqsToTerms eqs
  (absEqs, absAllVars) = abstractEqs $ abstractVars (eqs, allVars)
  (acSystem, homSystem) = splitSystem (isAnyHom . eqLHS) absEqs
  solvedSystems = solveDisjointSystems sortOf (acSystem, homSystem) (acUnifier, homUnifier) (getAllPartitions absAllVars)
  in combineDisjointSystems solvedSystems
  where
    acUnifier es = unsafePerformIO $ UM.unifyViaMaude mhnd (sortOfMConst sortOf) es
    homUnifier = unifyHomomorphicLTermWrapper (sortOfMConst sortOf)

abstractVars :: IsConst c => ([Equal (LTerm c)], [LVar]) -> ([Equal (LTerm c)], [LVar])
abstractVars ([], allVars) = ([], allVars)
abstractVars (e:es, allVars) = case findAlienSubTerm e of
  Just (alienSubterm, applyToOneSide) -> let
    -- TODO: can be improved to LSortMsg or LSortNat but algorithm would then need to be adapted
    newVar = getNewSimilarVar (LVar "abstractVar" LSortMsg 0) allVars
    newE = applyToOneSide (substituteTermWithVar alienSubterm newVar) e
    in abstractVars (Equal alienSubterm (varTerm newVar) : newE : es, newVar : allVars)
  Nothing -> let (newEs, totVars) = abstractVars (es, allVars)
    in (e : newEs, totVars)

findAlienSubTerm :: IsConst c => Equal (LTerm c) -> Maybe (LTerm c, (LTerm c -> LTerm c) -> Equal (LTerm c) -> Equal (LTerm c))
findAlienSubTerm eq = case
    (findAlienSubTerm' (isAnyHom (eqLHS eq)) (eqLHS eq),
     findAlienSubTerm' (isAnyHom (eqRHS eq)) (eqRHS eq)) of
  (Just alienTerm, _) -> Just (alienTerm, \f e -> Equal (f (eqLHS e)) (eqRHS e))
  (_, Just alienTerm) -> Just (alienTerm, \f e -> Equal (eqLHS e) (f (eqRHS e)))
  _                   -> Nothing

findAlienSubTerm' :: IsConst c => Bool -> LTerm c -> Maybe (LTerm c)
findAlienSubTerm' b t = case viewTerm t of
  Lit (Var _) -> Nothing
  Lit (Con _) -> Nothing -- if isAnyHom t /= b then Just t else Nothing
  FApp _ args -> if isAnyHom t /= b then Just t else case mapMaybe (findAlienSubTerm' b) args of
    []    -> Nothing
    (e:_) -> Just e

substituteTermWithVar :: IsConst c => LTerm c -> LVar -> LTerm c -> LTerm c
substituteTermWithVar tToSub newV t = if tToSub == t then varTerm newV else case viewTerm t of
  Lit (Var _)      -> t
  Lit (Con _)      -> t
  FApp funsym args -> termViewToTerm (FApp funsym (map (substituteTermWithVar tToSub newV) args))

abstractEqs :: IsConst c => ([Equal (LTerm c)], [LVar]) -> ([Equal (LTerm c)], [LVar])
abstractEqs ([], allVars) = ([], allVars)
abstractEqs (e:es, allVars) = if isLit (eqLHS e) || isLit (eqRHS e)
    || isAnyHom (eqLHS e) == isAnyHom (eqRHS e)
  then let (newEs, newVars) = abstractEqs (es, allVars) in (e : newEs, newVars)
  else let
    newVar = getNewSimilarVar (LVar "splitVar" LSortMsg 0) allVars
    (newEs, newVars) = abstractEqs (es, newVar : allVars)
  in (Equal (varTerm newVar) (eqLHS e) : Equal (varTerm newVar) (eqRHS e) : newEs, newVars)

getAllPartitions :: [a] -> [[[a]]]
getAllPartitions [] = [[]]
getAllPartitions (x : xs) = concatMap (insert x) (getAllPartitions xs)
  where
    insert :: a -> [[a]] -> [[[a]]]
    insert x' [] = [[[x']]]
    insert x' (ys : yss) = ((x' : ys) : yss) : map (ys : ) (insert x' yss)

splitSystem :: IsConst c => (Equal (LTerm c) -> Bool) -> [Equal (LTerm c)] -> EquationPair c
splitSystem fBool = foldr (\eq (eqL, eqR) -> if fBool eq then (eqL, eq:eqR) else (eq:eqL, eqR)) ([],[])

type EquationPair c = ([Equal (LTerm c)], [Equal (LTerm c)])

type MConstUnifierPair c = ([Equal (LTerm (MConst c))] -> [LSubstVFresh (MConst c)]
                          , [Equal (LTerm (MConst c))] -> [LSubstVFresh (MConst c)])

type VarOrdUnifierPair c = ([LVar], [LSubstVFresh c], [LSubstVFresh c])

solveDisjointSystems :: IsConst c => (c -> LSort) -> EquationPair c -> MConstUnifierPair c
  -> [[[LVar]]] -> VarOrdUnifierPair c
solveDisjointSystems _ _ _ [] = ([], [], [])
solveDisjointSystems sortOf sys unifiers (vP:varPartitions) = let
    sys' = applyVarPartition vP sys
    partitionVars = map head vP
    varIndexes = getAll01Maps partitionVars
  in case solveDisjointSystemsWithPartition sortOf sys' unifiers partitionVars varIndexes of
    Just substs -> substs
    Nothing     -> solveDisjointSystems sortOf sys unifiers varPartitions
  where
    applyVarPartition :: IsConst c => [[LVar]] -> EquationPair c -> EquationPair c
    applyVarPartition [] newSys = newSys
    applyVarPartition (vClass:vClasses) newSys = if length vClass == 1
      then applyVarPartition vClasses newSys
      else applyVarPartition vClasses (applyToSystem (vClassSubst vClass) newSys)
    vClassSubst :: IsConst c => [LVar] -> Subst c LVar
    vClassSubst vClass = substFromList $ map (\v -> (v, varTerm $ head vClass)) (tail vClass)
    applyToSystem :: IsConst c => Subst c LVar -> EquationPair c -> EquationPair c
    applyToSystem subst (sysL, sysR) = ((map . fmap) (applyVTerm subst) sysL,
                                        (map . fmap) (applyVTerm subst) sysR)
    getAll01Maps :: [a] -> [[(a, Int)]]
    getAll01Maps = mapM (\x -> [(x, 0), (x, 1)])

solveDisjointSystemsWithPartition :: IsConst c => (c -> LSort) -> EquationPair c -> MConstUnifierPair c 
  -> [LVar] -> [[(LVar, Int)]] -> Maybe (VarOrdUnifierPair c)
solveDisjointSystemsWithPartition _ _ _ _ [] = Nothing
solveDisjointSystemsWithPartition sortOf sys (unifierL, unifierR) vars (vIndex:varIndexes) = let
    (sysWithVarIndexL, sysWithVarIndexR) = applyVarConstToSys vIndex sys
    (solvedSysL, solvedSysR) = (unifierL sysWithVarIndexL, unifierR sysWithVarIndexR)
    solvedSysL' = map (map (second fromMConst) . substToListVFresh) solvedSysL
    solvedSysR' = map (map (second fromMConst) . substToListVFresh) solvedSysR
    (corrP, solvedSysL'', solvedSysR'') =
      getFirstNonEmptyPermutation (permutations vars) (solvedSysL', solvedSysR')
  -- NOTE: Maybe need to check for sorts because vor new variables etc.
  in if not (null solvedSysL)   && not (null solvedSysR)
     && not (null solvedSysL'') && not (null solvedSysR'')
  then Just (corrP, map substFromListVFresh solvedSysL'', map substFromListVFresh solvedSysR'')
  else solveDisjointSystemsWithPartition sortOf sys (unifierL, unifierR) vars varIndexes
  where
    applyVarConstToSys :: IsConst c => [(LVar, Int)] -> EquationPair c -> EquationPair (MConst c)
    applyVarConstToSys varIndex (sysL, sysR) = let
      vars0 = map fst $ filter (\ind -> snd ind == 0) varIndex
      vars1 = map fst $ filter (\ind -> snd ind == 1) varIndex
      in ((map . fmap) (toMConstVarList vars0) sysL,
          (map . fmap) (toMConstVarList vars1) sysR)
    -- NOTE: can be implemented more efficiently by checking that combined substitution 
    -- is circle free when looking at variabes.
    getFirstNonEmptyPermutation :: IsConst c => [[LVar]]
      -> ([[(LVar, LTerm c)]], [[(LVar, LTerm c)]])
      -> ([LVar], [[(LVar, LTerm c)]], [[(LVar, LTerm c)]])
    getFirstNonEmptyPermutation [] (_, _) = ([], [],[])
    getFirstNonEmptyPermutation (p:ps) (substsL,substsR) = let
        substsL' = linearRestriction p substsL
        substsR' = linearRestriction p substsR
      in if not (null substsL') && not (null substsR')
      -- NOTE: we reverse p as we look at linear restrictions in reverse order
      then (reverse p, substsL', substsR')
      else getFirstNonEmptyPermutation ps (substsL,substsR)
    linearRestriction :: IsConst c => [LVar] -> [[(LVar, LTerm c)]] -> [[(LVar, LTerm c)]]
    linearRestriction p = filter (linearRestriction' p)
    linearRestriction' :: IsConst c => [LVar] -> [(LVar, LTerm c)] -> Bool
    linearRestriction' p = all (\(varL, termR) -> all (\v -> v `notElem` varsVTerm termR) (takeWhile (/= varL) p))

-- TODO
combineDisjointSystems :: IsConst c => VarOrdUnifierPair c -> [LSubstVFresh c]
combineDisjointSystems sys = [emptySubstVFresh]

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
      Just ms -> reader $ matchTermChoose ms
  where
    trace' res = trace
      (unlines $ ["matchLTerm: "++ show matchProblem, "result = "++  show res])
      res

    matchTermChoose ms hnd = trace' $
      case runState (runExceptT match) M.empty of
          (Left NoMatcher, _)  -> []
          (Left ACProblem, _)  ->
              unsafePerformIO (UM.matchViaMaude hnd sortOf matchProblem)
          (Left HomomorphicProblem, _) ->
              maybeToList (matchHomomorphicLTerm sortOf ms)
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
       -- Special cases for builtin naturals: Make sure to perform unification
       -- via Maude if we have 1:nat on the left-/right-hand side.
       (FApp (NoEq lfsym) [], FApp (AC NatPlus) _) ->
          guard (lfsym == natOneSym) >> tell [Equal l r]
       (FApp (AC NatPlus) _, FApp (NoEq rfsym) []) ->
          guard (rfsym == natOneSym) >> tell [Equal l r]
       -- Homomorphic cases (need to be handled here since next is the general case with guard)
       (FApp (NoEq lfsym) _, FApp (NoEq rfsym) _) | lfsym /= rfsym ->
           -- chech failure rules
           guard (((isHomPair l && isHomEnc r) || (isHomEnc l && isHomPair r)) && failureHomomorphicRuleWrapper l r)
           >> tell [Equal l r]
       -- General cases / function application
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


data MatchFailure = NoMatcher | ACProblem | HomomorphicProblem

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
      (FApp (NoEq tfsym) _, FApp (NoEq pfsym) _) | tfsym /= pfsym ->
           guard ((isHomPair t && isHomEnc p) || (isHomEnc t && isHomPair p))
           >> throwError HomomorphicProblem
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
