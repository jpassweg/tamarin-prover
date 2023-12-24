{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
--
-- AC unification based on maude and free unification.
module Term.Unification (
  unifyHomACCLTerm

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

import           System.IO.Unsafe (unsafePerformIO)

import           Term.Term.FunctionSymbols
import           Term.Rewriting.Definitions
import           Term.Substitution
import qualified Term.Maude.Process as UM
import           Term.Maude.Process
                   (MaudeHandle, WithMaude, startMaude, getMaudeStats, mhMaudeSig, mhFilePath)
import           Term.Maude.Signature
import           Term.Unification.HomomorphicEncryption
import           Term.Unification.UnificationCombinator

import           Debug.Trace.Ignore


-- Unification modulo AC
----------------------------------------------------------------------

-- | @unifyLTerm sortOf eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLTermFactored :: (IsConst c)
                   => (c -> LSort)
                   -> [Equal (LTerm c)]
                   -> WithMaude (LSubst c, [SubstVFresh c LVar])
unifyLTermFactored sortOf eqs = reader $ \h -> (\res -> trace (unlines $ ["unifyLTerm: "++ show eqs, "result = "++  show res]) res) $
    if enableHom $ mhMaudeSig h
    then do solveWHom h $ execRWST unifWHom sortOf M.empty
    else do solve     h $ execRWST unif     sortOf M.empty
  where
    unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
    unifWHom = sequence [ unifyRawWithHom t p | Equal t p <- eqs ]
    solve h subst = case subst of
      Nothing        -> (emptySubst, [])
      Just (m, [])   -> (substFromMap m, [emptySubstVFresh])
      Just (m, leqs) -> (substFromMap m, unsafePerformIO (UM.unifyViaMaude h sortOf $ map (applyVTerm (substFromMap m) <$>) leqs))
    solveWHom h subst = case subst of
      Nothing        -> (emptySubst, [])
      Just (m, [])   -> (substFromMap m, [emptySubstVFresh])
      Just (m, leqs) -> (substFromMap m, prepareUnifyUnionDisjointTheories sortOf h $ map (applyVTerm (substFromMap m) <$>) leqs)

prepareUnifyUnionDisjointTheories :: IsConst c => (c -> LSort) -> MaudeHandle -> [Equal (LTerm c)] -> [LSubstVFresh c]
prepareUnifyUnionDisjointTheories sortOf mhnd eqs = let
    hasAC  = all (\(Equal l r) -> hasAny isACC l    && hasAny isACC r   ) eqs
    hasHom = all (\(Equal l r) -> hasAny isAnyHom l && hasAny isAnyHom r) eqs
  in case (hasAC, hasHom) of
    (_,     False) -> unsafePerformIO (UM.unifyViaMaude mhnd sortOf eqs)
    (False, True)  -> unifyHomLTerm sortOf eqs
    (True,  True)  -> unifyHomACCLTerm sortOf mhnd eqs

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
      Just ms -> reader $ matchTerm ms 
  where
    trace' res = trace
      (unlines $ ["matchLTerm: "++ show matchProblem, "result = "++  show res])
      res

    matchTerm ms hnd = trace' $
      case runState (runExceptT match) M.empty of
          (Left NoMatcher, _)  -> []
          (Left ACProblem, _) | not $ enableHom $ mhMaudeSig hnd ->
              unsafePerformIO (UM.matchViaMaude hnd sortOf matchProblem)
          (Left ACProblem, _) | not $ any (\m -> hasAny isAnyHom (fst m) || hasAny isAnyHom (snd m)) ms ->
              unsafePerformIO (UM.matchViaMaude hnd sortOf matchProblem)
          (Left ACProblem, _) ->
              matchHomACCLTerm sortOf hnd matchProblem
          (Left HomProblem, _) | not $ any (\m -> hasAny isACC (fst m) || hasAny isACC (snd m)) ms ->
              matchHomLTerm sortOf matchProblem
          (Left HomProblem, _) ->
              matchHomACCLTerm sortOf hnd matchProblem
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

-- | Unify two 'LTerm's with delayed AC-unification and delayed Homomorphic Encryption unification.
unifyRawWithHom :: IsConst c => LTerm c -> LTerm c -> UnifyRaw c ()
unifyRawWithHom l0 r0 = do
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
       (FApp (NoEq _) _, FApp (NoEq _) _) | isAnyHom l || isAnyHom r  ->
           guard (fastTestUnifiableHom l r)
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

data MatchFailure = NoMatcher | ACProblem | HomProblem

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
      (FApp (NoEq _) _, FApp (NoEq _) _) | isAnyHom t || isAnyHom p ->
           throwError HomProblem
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
