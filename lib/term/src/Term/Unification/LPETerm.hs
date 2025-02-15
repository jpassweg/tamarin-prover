{-# LANGUAGE ViewPatterns       #-}

module Term.Unification.LPETerm (
  -- * Homomorphic Representation types
    LPETerm(..)
  , PRepresentation(..)
  , ERepresentation

  -- * Helper functions
  , viewTermPE

  -- * Homomorphic Representation functions
  , toLPETerm
  , positionsWithTerms
  , pPosition
  , ePosition
  , positionsIncompatible
  , fromPRepresentation
  , fromERepresentation

  -- * Norm functions
  , normHom
  , nfHom
  , nfHomHEPlus
  , normHomHEPlus

  -- * Functions for debuggin Homomorphic Representations
  , findPurePPositions
  , findPenukEPositions
  , maximalPositions
  , buildPRepresentation
  , buildERepresentation
) where

import Data.Bifunctor (first, second)

import Term.LTerm (
  LTerm, IsConst, Lit(..), LVar,
  TermView(Lit, FApp), TermView2(FHenc, FPair),
  viewTerm, viewTerm2, termViewToTerm, fAppHomEnc, isHomEnc, fAppPair, isFst, isPair, isSnd, isHomDec, hasSameHomKey
  ) 
-- IsConst from Term.VTerm
-- TermView(Lit, FApp), TermView2(FHenc), 
-- viewTerm, viewTerm2, termViewToTerm from Term.Term.Raw
-- fAppHomEnc, isHomEnc from Term.Term

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

-- LNPETerms functions for more simplicity
------------------------------------------

viewTermPE :: IsConst c => LPETerm c -> TermView (Lit c LVar)
viewTermPE = viewTerm . lTerm

-- Homomorphic encryption and LNPETerms specific functions
----------------------------------------------------------

-- | Builds P and E Representation for matching with homomorphic patterns 
toLPETerm :: (IsConst c) => LTerm c -> LPETerm c
toLPETerm t = LPETerm t (buildPRepresentation t) (buildERepresentation t)

-- | Returns All subterms (including the term itself) given a term with their positions
positionsWithTerms :: (IsConst c) => LTerm c -> [(String, LTerm c)]
positionsWithTerms = positionsWithTerms' ""

-- | used by positionsWithTerms
positionsWithTerms' :: (IsConst c) => String -> LTerm c -> [(String, LTerm c)]
positionsWithTerms' pos t = case viewTerm t of
  (Lit _)       -> [(pos,t)]
  (FApp _ args) -> (pos,t) : concat (zipWith argFunc [1..] args)
  where
    argFunc :: (IsConst c) => Int -> LTerm c -> [(String, LTerm c)]
    argFunc ind = positionsWithTerms' (pos ++ show ind)

-- | Returns the pposition used for Homomorphic Pattern rules
pPosition :: (IsConst c) => String -> LTerm c -> String
pPosition [] _ = ""
pPosition (i:q) t = let ind = read [i] - 1 in case viewTerm2 t of
  _ | ind >= 2 -> "N"
  FPair t1 t2  -> i : pPosition q ([t1,t2] !! ind)
  FHenc t1 t2     ->     pPosition q ([t1,t2] !! ind)
  _               -> "N"

-- | Returns the eposition used for Homomorphic Pattern rules
ePosition :: (IsConst c) => String -> LTerm c -> String
ePosition [] _ = ""
ePosition (i:q) t = let ind = read [i] - 1 in case viewTerm2 t of
  _ | ind >= 2 -> "N"
  FHenc t1 t2     -> i : ePosition q ([t1,t2] !! ind)
  FPair t1 t2  ->     ePosition q ([t1,t2] !! ind)
  _               -> "N"

-- | Returns if two positions are incompatible
positionsIncompatible :: (IsConst c) => String -> LTerm c -> String -> LTerm c -> Bool
positionsIncompatible q1 t1 q2 t2 =
     properPrefix (pPosition q1 t1) (pPosition q2 t2)
  || properPrefix (pPosition q2 t2) (pPosition q1 t1)
  ||  ( pPosition q1 t1 == pPosition q2 t2
     && ePosition q1 t1 /= ePosition q2 t2
     && all ('1' ==) (ePosition q1 t1)
     && all ('1' ==) (ePosition q2 t2) )

-- | Returns all positions in t for which epos==""
findPurePPositions :: (IsConst c) => LTerm c -> [(String, LTerm c)]
findPurePPositions t = filter (\(p,_) -> ePosition p t == "") $ positionsWithTerms t

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

{-
-- | Function to test if strings used in a P-Representation are valid
-- Note: not used
validBitString :: [String] -> Bool
validBitString [""] = True
validBitString s = contains12Pattern s
  && validBitString (getOnes s)
  && validBitString (getTwos s)
  where
    contains12Pattern strings = null (dropWhile (\x -> head x =='2')
      $ dropWhile (\x -> head x == '1') strings)
      && any (\x -> head x == '1') strings
      && any (\x -> head x == '2') strings
    getOnes strings = map tail $ takeWhile (\x -> head x=='1') strings
    getTwos strings = map tail $ dropWhile (\x -> head x=='1') strings
-}

-- | Returns all positions that are not prefixes of other positions
maximalPositions :: (IsConst c) => [(String, LTerm c)] -> [(String, LTerm c)]
maximalPositions ps = filter (\p -> not $ any (properPrefix (fst p) . fst) ps) ps

-- | returns P representation for Homomorphic Patterns
buildPRepresentation :: (IsConst c) => LTerm c -> PRepresentation c
buildPRepresentation t = uncurry PRep $ unzip
  $ map (second buildERepresentation) $ maximalPositions $ findPurePPositions t

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
  else fAppPair (fRep takeWhile, fRep dropWhile )
  where
    fRep fWhile = fromPRepresentation $ uncurry PRep $ unzip 
      $ map (first (\s -> if s == "" then "" else tail s)) 
      $ fWhile (\(a,_) -> head a == '1') $ zip (eRepsString p) (eRepsTerms p)

-- | rebuilds a LTerm from the P Representation generated by buildPRepresentationOnly
fromPRepresentationOnly :: (IsConst c) => ([String],[LTerm c]) -> LTerm c
fromPRepresentationOnly (s,p) =
  if s == [""]
  then head p
  else fAppPair (
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
-- Assumes Term can not be empty (ERepresentation would then be empty list)
fromERepresentation :: (IsConst c) => ERepresentation c -> LTerm c
fromERepresentation e = if length e == 1 then head e
  else fAppHomEnc (fromERepresentation (init e), last e)

-- Norm related functions for Homomorphic encryption
----------------------------------------------------

-- | @normHom t@ normalizes the term @t@ modulo the homomorphic rule 
-- henc(<x1,x2>,k) -> <henc(x1,k),henc(x2,k)>
normHom :: (IsConst c) => LTerm c -> LTerm c
normHom t = case viewTerm t of
    FApp _ [t1, t2] | isHomEnc t -> let 
      t1N = normHom t1 
      t2N = normHom t2
      in case viewTerm2 t1N of
        FPair t11N t12N -> fAppPair (normHom $ fAppHomEnc (t11N, t2N), normHom $ fAppHomEnc (t12N, t2N))
        _               -> fAppHomEnc (t1N, t2N)
    FApp funsym ts -> termViewToTerm (FApp funsym (map normHom ts))
    Lit _ -> t

nfHom :: (IsConst c) => LTerm c -> Bool
nfHom t = case viewTerm t of
  FApp _ [viewTerm2 -> FPair _ _, _] | isHomEnc t -> False
  FApp _ ts                                          -> all nfHom ts
  Lit _                                              -> True

-- | returns if the term is in normal form modulo HE+
nfHomHEPlus :: (IsConst c) => LTerm c -> Bool
nfHomHEPlus t = case viewTerm t of
    FApp _ [t1   ] | isFst t    && isPair t1           -> False
    FApp _ [t1   ] | isSnd t    && isPair t1           -> False
    FApp _ [t1, _] | isHomDec t && hasSameHomKey t t1  -> False -- TODO: not sure though
    FApp _ [t1, _] | isHomEnc t && isPair t1           -> False
    FApp _ [t1, _] | isHomDec t && hasSameHomKeys t t1 -> False -- TODO: not sure though
    FApp _ ts -> all nfHomHEPlus ts
    Lit _ -> True
  where
    hasSameHomKeys :: (IsConst c) => LTerm c -> LTerm c -> Bool
    hasSameHomKeys t1 t2 =
          all (hasSameHomKey t1) (snd $ buildPRepresentationOnly t2) &&
          all isHomEnc (snd $ buildPRepresentationOnly t2)

-- | @normHom t@ normalizes the term @t@ modulo HE+
normHomHEPlus :: (IsConst c) => LTerm c -> LTerm c
normHomHEPlus t = case viewTerm t of
    FApp _ [t1    ] | isFst t    && isPair t1           -> nH $ getFst t1
    FApp _ [t1    ] | isSnd t    && isPair t1           -> nH $ getSnd t1
    FApp _ [t1, _ ] | isHomDec t && hasSameHomKey t t1  -> nH t1
    FApp _ [t1, t2] | isHomEnc t && isPair t1           ->
      nH $ fAppPair (nH $ fAppHomEnc (nH $ getFst t1, nH t2), nH $ fAppHomEnc (nH $ getSnd t1, nH t2))
    FApp _ [t1, _ ] | isHomDec t && hasSameHomKeys t t1 ->
      nH $ fromPRepresentationOnly $ removeHomKeys $ buildPRepresentationOnly t1
    FApp funsym ts                                      ->
      termViewToTerm (FApp funsym (map nH ts))
    Lit _ -> t
  where
    nH = normHomHEPlus
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