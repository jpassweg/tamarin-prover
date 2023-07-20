module Term.Homomorphism.LNPETerm (
  LNPETerm(..)
  , PRepresentation(..)
  , ERepresentation

  -- * Homomorphic Representations
  , toLNPETerm
  , positionsWithTerms
  , pPosition
  , ePosition
  , positionsIncompatible
  , fromPRepresentation
  , fromERepresentation
  , isHenc
  , getHencSym

  -- * For debuggin Homomorphic Representations
  , findPurePPositions
  , findPenukEPositions
  , maximalPositions
  , buildPRepresentation
  , buildERepresentation
) where

import Term.LTerm
import Term.Builtin.Signature

-- E representation as defined in the cap unification paper
type ERepresentation = [LNTerm]

-- P representation as defined in the cap unification paper
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

-- Homomorphic encryption and LNPETerms specific functions
----------------------------------------------------------

-- | Builds P and E Representation for matching with homomorphic patterns 
toLNPETerm :: LNTerm -> LNPETerm
toLNPETerm t = LNPETerm t (buildPRepresentation t) (buildERepresentation t)

-- | Returns All subterms given a term with their positions
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
    else "DIFF"
    else "ARGL"
  _ -> "NONF"

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

isHenc :: FunSym -> Bool
isHenc funsym = funsym == NoEq hencSym

getHencSym :: FunSym
getHencSym = NoEq hencSym

positionsIncompatible :: String -> LNTerm -> String -> LNTerm -> Bool
positionsIncompatible q1 t1 q2 t2 = properPrefix (pPosition q1 t1) (pPosition q2 t2)
  || properPrefix (pPosition q2 t2) (pPosition q1 t1)
  || ((pPosition q1 t1) == (pPosition q2 t2) 
      && (ePosition q1 t1) /= (ePosition q2 t2)
      && all ((==) '1') (ePosition q1 t1) 
      && all ((==) '1') (ePosition q2 t2))

-- | Returns all positions in t for which epos==""
findPurePPositions :: LNTerm -> [(String, LNTerm)]
findPurePPositions t = 
  filter (\(p,_) -> ePosition p t == "")
  $ positionsWithTerms t

-- | Returns all positions in t for which ppos=="" and are not position under a key
findPenukEPositions :: LNTerm -> [(String, LNTerm)]
findPenukEPositions t = 
  filter (\(p,_) -> pPosition p t == "" && penukPositions p) 
  $ positionsWithTerms t
  where 
    penukPositions [] = True
    penukPositions (x:xs) = (x == '1' && penukPositions xs) || (x == '2' && null xs)

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

-- gonna be very hacky
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

-- very hacky
fromERepresentation :: ERepresentation -> LNTerm
fromERepresentation e = if length e == 1
  then head e
  else (FAPP (getHencSym) ([fromERepresentation (init e)] ++ [last e]))