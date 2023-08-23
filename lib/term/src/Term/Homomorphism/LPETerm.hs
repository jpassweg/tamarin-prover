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

  -- * Norm functions
  --, nfHomomorphicHEPlus
  --, normHomomorphicHEPlus
  , normHomomorphic
  --, buildPRepresentationOnly
  --, fromPRepresentationOnly

  -- * Functions for debuggin Homomorphic Representations
  , findPurePPositions
  , findPenukEPositions
  , maximalPositions
  , buildPRepresentation
  , buildERepresentation
) where

import Term.LTerm (
  LTerm, Lit(Var, Con), IsConst, TermView(Lit, FApp), 
  viewTerm, termViewToTerm, fAppPair, 
  fAppHenc, isPair, isFst, isSnd, isHomEnc, isHomDec, hasSameHomKey)
-- Term, TermView(Lit, FApp), viewTerm, termViewToTerm, fAppNoEq come from Term.Term.Raw
-- Lit(Var, Con), IsConst comes from Term.VTerm
-- FunSym(NoEq), fstSym, sndSym, homEncSym, homDecSym comes from Term.Term.FunctionSymbols
-- fAppPair, fAppHenc, isHomEnc, hasSameHomKey, isPair come from Term.Term

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
-- TODO: can be done more elegantly with viewTerm2
pPosition :: (IsConst c) => String -> LTerm c -> String
pPosition [] _ = ""
pPosition (i:q) t = case viewTerm t of
  FApp _ args -> 
    if length args > read [i] - 1 
    then if isPair t 
    then [i] ++ (pPosition q $ args !! (read [i] - 1))
    else if isHomEnc t
    then pPosition q $ args !! (read [i] - 1)
    else "DIFF" -- different function symbol
    else "ARGL" -- argument length issue
  _ -> "NONF"   -- not a function symbol

-- | Returns the eposition used for Homomorphic Pattern rules
-- TODO: can be done more elegantly with viewTerm2
ePosition :: (IsConst c) => String -> LTerm c -> String
ePosition [] _ = ""
ePosition (i:q) t = case viewTerm t of
  FApp _ args -> 
    if length args > read [i] - 1
    then if isHomEnc t
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

-- | Function to test if strings used in a P-Representation are valid
-- Note: not used
validBitString :: [String] -> Bool
validBitString [""] = True
validBitString s = contains12Pattern s 
  && (validBitString $ getOnes s) 
  && (validBitString $ getTwos s) 
  where
    contains12Pattern strings = (null 
      $ dropWhile (\x -> (head x)=='2')
      $ dropWhile (\x -> (head x)=='1') strings)
      && any (\x -> (head x)=='1') strings
      && any (\x -> (head x)=='2') strings
    getOnes strings = map tail $ takeWhile (\x -> (head x)=='1') strings
    getTwos strings = map tail $ dropWhile (\x -> (head x)=='1') strings

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

-- | returns P representation without building E representation of subterms
buildPRepresentationOnly :: (IsConst c) => LTerm c -> ([String],[LTerm c])
buildPRepresentationOnly t = unzip $ maximalPositions $ findPurePPositions t

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

-- | rebuilds a LTerm from the P Representation generated by buildPRepresentationOnly
fromPRepresentationOnly :: (IsConst c) => ([String],[LTerm c]) -> LTerm c
fromPRepresentationOnly (s,p) =
  if s == [""]
  then head p
  else fAppPair(
      fromPRepresentationOnly $ sRep takeWhile
    , fromPRepresentationOnly $ sRep dropWhile )
  where
    sRep fWhile = 
      unzip $ map (\(a,b) -> (safeTail a, b)) 
      $ fWhile (\(a,_) -> (head a) == '1') $ zip s p
    safeTail xs 
      | null xs   = ""
      | otherwise = tail xs

-- | rebuilds a LTerm from a E Representation
fromERepresentation :: (IsConst c) => ERepresentation c -> LTerm c
fromERepresentation e = if length e == 1
  then head e
  else fAppHenc (fromERepresentation (init e), last e)

-- Norm related functions for Homomorphic encryption
----------------------------------------------------

-- | returns if the term is in normal form modulo HE+
nfHomomorphicHEPlus :: (IsConst c) => LTerm c -> Bool
nfHomomorphicHEPlus t = case viewTerm t of
    FApp _ [t1   ] | isFst t    && isPair t1           -> False
    FApp _ [t1   ] | isSnd t    && isPair t1           -> False
    FApp _ [t1, _] | isHomDec t && hasSameHomKey t t1  -> False
    FApp _ [t1, _] | isHomEnc t && isPair t1           -> False
    FApp _ [t1, _] | isHomDec t && hasSameHomKeys t t1 -> False
    FApp _ ts -> all nfHomomorphicHEPlus ts
    Lit _ -> True
  where
    hasSameHomKeys :: (IsConst c) => LTerm c -> LTerm c -> Bool
    hasSameHomKeys t1 t2 = 
          all (hasSameHomKey t1) (snd $ buildPRepresentationOnly t2) &&
          all isHomEnc (snd $ buildPRepresentationOnly t2)

-- | @normHomomorphic t@ normalizes the term @t@ modulo the homomorphic rule henc(<x1,x2>,k) -> <henc(x1,k),henc(x2,k)>
normHomomorphic :: (IsConst c) => LTerm c -> LTerm c
normHomomorphic t = case viewTerm t of
    FApp _ [t1, t2] | isHomEnc t && isPair t1           -> 
      fAppPair(nH $ fAppHenc (nH $ getFst t1, nH t2), nH $ fAppHenc (nH $ getSnd t1, nH t2))
    FApp funsym ts                                      -> 
      termViewToTerm (FApp funsym (map nH ts))
    Lit _ -> t
  where
    nH = normHomomorphic
    getFst :: (IsConst c) => LTerm c -> LTerm c
    getFst te = case viewTerm te of
      FApp _ [t1, _] -> t1
      _ -> te
    getSnd :: (IsConst c) => LTerm c -> LTerm c
    getSnd te = case viewTerm te of
      FApp _ [_, t2] -> t2
      _ -> te

-- | @normHomomorphic t@ normalizes the term @t@ modulo HE+
normHomomorphicHEPlus :: (IsConst c) => LTerm c -> LTerm c
normHomomorphicHEPlus t = case viewTerm t of
    FApp _ [t1    ] | isFst t    && isPair t1           -> nH $ getFst t1
    FApp _ [t1    ] | isSnd t    && isPair t1           -> nH $ getSnd t1
    FApp _ [t1, _ ] | isHomDec t && hasSameHomKey t t1  -> nH t1
    FApp _ [t1, t2] | isHomEnc t && isPair t1           -> 
      fAppPair(nH $ fAppHenc (nH $ getFst t1, nH t2), nH $ fAppHenc (nH $ getSnd t1, nH t2))
    FApp _ [t1, _ ] | isHomDec t && hasSameHomKeys t t1 -> 
      nH $ fromPRepresentationOnly $ removeHomKeys $ buildPRepresentationOnly t1
    FApp funsym ts                                      -> 
      termViewToTerm (FApp funsym (map nH ts))
    Lit _ -> t
  where
    nH = normHomomorphicHEPlus
    getFst :: (IsConst c) => LTerm c -> LTerm c
    getFst te = case viewTerm te of
      FApp _ [t1, _] -> t1
      _ -> te
    getSnd :: (IsConst c) => LTerm c -> LTerm c
    getSnd te = case viewTerm te of
      FApp _ [_, t2] -> t2
      _ -> te
    hasSameHomKeys :: (IsConst c) => LTerm c -> LTerm c -> Bool
    hasSameHomKeys t1 t2 = 
          all (hasSameHomKey t1) (snd $ buildPRepresentationOnly t2) &&
          all isHomEnc (snd $ buildPRepresentationOnly t2)
    removeHomKeys :: (IsConst c) => ([String], [LTerm c]) -> ([String], [LTerm c])
    removeHomKeys (s,ps) = (s, map getFst ps)