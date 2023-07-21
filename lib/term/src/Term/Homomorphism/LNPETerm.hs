module Term.Homomorphism.LNPETerm (
  -- * Homomorphic Representation types
  LNPETerm(..)
  , PRepresentation(..)
  , ERepresentation

  -- * Homomorphic Representation functions
  , toLNPETerm
  , positionsWithTerms
  , pPosition
  , ePosition
  , positionsIncompatible
  , fromPRepresentation
  , fromERepresentation

  -- * Functions to better access the Homomorphic Encrytion Signature
  , isHenc
  , fAppHenc

  -- * Functions for debuggin Homomorphic Representations
  , findPurePPositions
  , findPenukEPositions
  , maximalPositions
  , buildPRepresentation
  , buildERepresentation
) where

import Term.LTerm (
  LNTerm, Term, Lit(Var, Con), TermView(Lit, FApp), FunSym(NoEq), 
  viewTerm, fAppNoEq, fAppPair, isPair)
-- Term, TermView(Lit, FApp), viewTerm, fAppNoEq come from Term.Term.Raw
-- Lit(Var, Con) comes from Term.VTerm
-- FunSym(NoEq) comes from Term.Term.FunctionSymbols
-- fAppPair, isPair come from Term.Term

-- The signature for homomorphic encryption
import Term.Builtin.Signature (hencSym)

-- New Types used for Unification modulo Homomorphic Encrpytion
---------------------------------------------------------------

-- | E representation as defined in the cap unification paper
type ERepresentation = [LNTerm]

-- | P representation as defined in the cap unification paper
--   Since rules applied in the Unification modulo Homomorphic Encrpytion algorithm
--   (namely the homomorphic patterns) compare either ERepresentation or ERepresentations
--   inside a PRepresentation, we directly store the terms inside the PRepresentation as
--   ERepresentations of the terms.
data PRepresentation = PRep 
    { eRepsString :: [String]
    , eRepsTerms :: [ERepresentation] 
    }
    deriving (Show, Eq, Ord)

-- | Terms used for proving; i.e., variables fixed to logical variables
--   and constants to Names.
--   Additionally contains some position information for Homomorphic encryption rules
data LNPETerm = LNPETerm
      { lnTerm :: LNTerm
      , pRep :: PRepresentation
      , eRep :: ERepresentation
      } 
      deriving (Show, Eq, Ord)

-- Cleaner access to Homomorphic Encryption Function Symbols
------------------------------------------------------------

-- | Smart constructor for a homomorphic encryption.
fAppHenc :: (Term a, Term a) -> Term a
fAppHenc (x,y) = fAppNoEq hencSym [x, y]

-- | Returns 'True' iff the @funsym@ matches the function symbol of homomorphic encryption.
isHenc :: FunSym -> Bool
isHenc funsym = funsym == (NoEq hencSym)

-- Homomorphic encryption and LNPETerms specific functions
----------------------------------------------------------

-- | Builds P and E Representation for matching with homomorphic patterns 
toLNPETerm :: LNTerm -> LNPETerm
toLNPETerm t = LNPETerm t (buildPRepresentation t) (buildERepresentation t)

-- | Returns All subterms (including the term itself) given a term with their positions
positionsWithTerms :: LNTerm -> [(String,LNTerm)]
positionsWithTerms t = positionsWithTerms' t ""

-- | used by positionsWithTerms
positionsWithTerms' :: LNTerm -> String -> [(String,LNTerm)]
positionsWithTerms' t p = case viewTerm t of
  (Lit(Con _))  -> [(p,t)]
  (Lit(Var _))  -> [(p,t)]
  (FApp _ args) -> [(p,t)] ++ (concat $ zipWith argFunc args [1..])
  where
    argFunc :: LNTerm -> Int -> [(String, LNTerm)]
    argFunc arg ind = positionsWithTerms' arg (p ++ (show ind))

-- | Returns the pposition used for Homomorphic Pattern rules
pPosition :: String -> LNTerm -> String
pPosition [] _ = ""
pPosition (i:q) t = case viewTerm t of
  FApp funsym args -> 
    if length args > read [i] - 1 
    then if isPair t 
    then [i] ++ (pPosition q $ args !! (read [i] - 1))
    else if isHenc funsym
    then pPosition q $ args !! (read [i] - 1)
    else "DIFF" -- different function symbol
    else "ARGL" -- argument length issue
  _ -> "NONF"   -- not a function symbol

-- | Returns the eposition used for Homomorphic Pattern rules
ePosition :: String -> LNTerm -> String
ePosition [] _ = ""
ePosition (i:q) t = case viewTerm t of
  FApp funsym args -> 
    if length args > read [i] - 1
    then if isHenc funsym
    then [i] ++ (ePosition q $ args !! (read [i] - 1))
    else if isPair t
    then ePosition q $ args !! (read [i] - 1)
    else "DIFF"
    else "ARGL"
  _ -> "NONF"

-- | Returns if two positions are incompatible
positionsIncompatible :: String -> LNTerm -> String -> LNTerm -> Bool
positionsIncompatible q1 t1 q2 t2 = 
     properPrefix (pPosition q1 t1) (pPosition q2 t2)
  || properPrefix (pPosition q2 t2) (pPosition q1 t1)
  || ((pPosition q1 t1) == (pPosition q2 t2) 
      && (ePosition q1 t1) /= (ePosition q2 t2)
      && all ((==) '1') (ePosition q1 t1) 
      && all ((==) '1') (ePosition q2 t2))

-- | Returns all positions in t for which epos==""
findPurePPositions :: LNTerm -> [(String, LNTerm)]
findPurePPositions t = 
  filter (\(p,_) -> ePosition p t == "") $ positionsWithTerms t

-- | Returns all positions in t for which ppos=="" and are not position under a key
findPenukEPositions :: LNTerm -> [(String, LNTerm)]
findPenukEPositions t = 
  filter (\(p,_) -> pPosition p t == "" && penukPositions p) $ positionsWithTerms t
  where 
    penukPositions [] = True
    penukPositions (x:xs) = (x == '1' && penukPositions xs) || (x == '2' && null xs)

-- | @properPrefix s1 s2@ returns True iff @s1@ is a proper prefix of @s2@ 
properPrefix :: String -> String -> Bool
properPrefix _ [] = False
properPrefix [] _ = True
properPrefix (s11:s1) (s21:s2) = s11 == s21 && properPrefix s1 s2

-- | Returns all positions that are not prefixes of other positions
maximalPositions :: [(String, LNTerm)] -> [(String, LNTerm)]
maximalPositions ps = 
  filter (\p -> not $ any (properPrefix $ fst p) $ map fst ps) ps

-- | returns P representation for Homomorphic Patterns
buildPRepresentation :: LNTerm -> PRepresentation
buildPRepresentation t = 
  (uncurry PRep) $ unzip 
  $ map (\(a,b) -> (a, buildERepresentation b)) 
  $ maximalPositions $ findPurePPositions t

-- | returns E representation for Homomorphic Patterns
buildERepresentation :: LNTerm -> ERepresentation
buildERepresentation t = map snd $ maximalPositions $ findPenukEPositions t

-- | rebuilds a LNTerm from a P Representation
fromPRepresentation :: PRepresentation -> LNTerm
fromPRepresentation p = 
  if eRepsString p == [""]
  then fromERepresentation $ head $ eRepsTerms p
  else fAppPair(
      fromPRepresentation $ sRep takeWhile
    , fromPRepresentation $ sRep dropWhile )
  where
    sRep fWhile = 
      (uncurry PRep) $ unzip 
      $ map (\(a,b) -> (safeTail a, b)) 
      $ fWhile (\(a,_) -> (head a) == '1')
      $ zip (eRepsString p) (eRepsTerms p)
    safeTail xs 
      | null xs   = ""
      | otherwise = tail xs

-- | rebuilds a LNTerm from a E Representation
fromERepresentation :: ERepresentation -> LNTerm
fromERepresentation e = if length e == 1
  then head e
  else fAppHenc (fromERepresentation (init e), last e)