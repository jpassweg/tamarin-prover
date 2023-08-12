module Term.Homomorphism.LPETerm (
  -- * Homomorphic Representation types
  LPETerm(..)
  , PRepresentation(..)
  , ERepresentation

  -- * Homomorphic Representation functions
  , toLPETerm
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
  , normHomomorphic
) where

import Term.LTerm (
  LTerm, Term, Lit(Var, Con), IsConst, TermView(Lit, FApp), FunSym(NoEq), 
  viewTerm, termViewToTerm, fAppNoEq, fAppPair, isPair)
-- Term, TermView(Lit, FApp), viewTerm, termViewToTerm, fAppNoEq come from Term.Term.Raw
-- Lit(Var, Con), IsConst comes from Term.VTerm
-- FunSym(NoEq) comes from Term.Term.FunctionSymbols
-- fAppPair, isPair come from Term.Term

-- The signature for homomorphic encryption
import Term.Builtin.Signature (hencSym)

-- New Types used for Unification modulo Homomorphic Encrpytion
---------------------------------------------------------------

-- | E representation as defined in the cap unification paper
type ERepresentation c = [LTerm c]

-- | P representation as defined in the cap unification paper
--   Since rules applied in the Unification modulo Homomorphic Encrpytion algorithm
--   (namely the homomorphic patterns) compare either ERepresentation or ERepresentations
--   inside a PRepresentation, we directly store the terms inside the PRepresentation as
--   ERepresentations of the terms.
data PRepresentation c = PRep 
    { eRepsString :: [String]
    , eRepsTerms :: [ERepresentation c] 
    }
    deriving (Show, Eq, Ord)

-- | Terms used for proving; i.e., variables fixed to logical variables
--   and constants to Names.
--   Additionally contains some position information for Homomorphic encryption rules
data LPETerm c = LPETerm
      { lTerm :: LTerm c
      , pRep  :: PRepresentation c
      , eRep  :: ERepresentation c
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
toLPETerm :: (IsConst c) => LTerm c -> LPETerm c
toLPETerm t = LPETerm t (buildPRepresentation t) (buildERepresentation t)

-- | Returns All subterms (including the term itself) given a term with their positions
positionsWithTerms :: (IsConst c) => LTerm c -> [(String, LTerm c)]
positionsWithTerms t = positionsWithTerms' t ""

-- | used by positionsWithTerms
positionsWithTerms' :: (IsConst c) => LTerm c -> String -> [(String, LTerm c)]
positionsWithTerms' t p = case viewTerm t of
  (Lit(Con _))  -> [(p,t)]
  (Lit(Var _))  -> [(p,t)]
  (FApp _ args) -> [(p,t)] ++ (concat $ zipWith argFunc args [1..])
  where
    argFunc :: (IsConst c) => LTerm c -> Int -> [(String, LTerm c)]
    argFunc arg ind = positionsWithTerms' arg (p ++ (show ind))

-- | Returns the pposition used for Homomorphic Pattern rules
pPosition :: (IsConst c) => String -> LTerm c -> String
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
ePosition :: (IsConst c) => String -> LTerm c -> String
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
positionsIncompatible :: (IsConst c) => String -> LTerm c -> String -> LTerm c -> Bool
positionsIncompatible q1 t1 q2 t2 = 
     properPrefix (pPosition q1 t1) (pPosition q2 t2)
  || properPrefix (pPosition q2 t2) (pPosition q1 t1)
  || ((pPosition q1 t1) == (pPosition q2 t2) 
      && (ePosition q1 t1) /= (ePosition q2 t2)
      && all ((==) '1') (ePosition q1 t1) 
      && all ((==) '1') (ePosition q2 t2))

-- | Returns all positions in t for which epos==""
findPurePPositions :: (IsConst c) => LTerm c -> [(String, LTerm c)]
findPurePPositions t = 
  filter (\(p,_) -> ePosition p t == "") $ positionsWithTerms t

-- | Returns all positions in t for which ppos=="" and are not position under a key
findPenukEPositions :: (IsConst c) => LTerm c -> [(String, LTerm c)]
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
maximalPositions :: (IsConst c) => [(String, LTerm c)] -> [(String, LTerm c)]
maximalPositions ps = 
  filter (\p -> not $ any (properPrefix $ fst p) $ map fst ps) ps

-- | returns P representation for Homomorphic Patterns
buildPRepresentation :: (IsConst c) => LTerm c -> PRepresentation c
buildPRepresentation t = 
  (uncurry PRep) $ unzip 
  $ map (\(a,b) -> (a, buildERepresentation b)) 
  $ maximalPositions $ findPurePPositions t

-- | returns E representation for Homomorphic Patterns
buildERepresentation :: (IsConst c) => LTerm c -> ERepresentation c
buildERepresentation t = map snd $ maximalPositions $ findPenukEPositions t

-- | rebuilds a LTerm from a P Representation
fromPRepresentation :: (IsConst c) => PRepresentation c -> LTerm c
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

-- | rebuilds a LTerm from a E Representation
fromERepresentation :: (IsConst c) => ERepresentation c -> LTerm c
fromERepresentation e = if length e == 1
  then head e
  else fAppHenc (fromERepresentation (init e), last e)

-- | @normHomomorphic t@ normalizes the term @t@ if the top function is the homomorphic encryption
normHomomorphic :: (IsConst c) => LTerm c -> LTerm c
normHomomorphic t = case viewTerm t of
  (FApp sym1 [t1, t2]) -> 
    case viewTerm t1 of
      (FApp _ [t11,t12]) ->
        if (isHenc sym1) && (isPair t1) 
        then fAppPair(fAppHenc (n t11, n t2), fAppHenc (n t12, n t2))
        else termViewToTerm $ FApp sym1 (map n [t1,t2])
      (_) -> termViewToTerm $ FApp sym1 (map n [t1,t2])
  (FApp sym args) -> termViewToTerm $ FApp sym (map n args)
  (_) -> t
  where
    n = normHomomorphic