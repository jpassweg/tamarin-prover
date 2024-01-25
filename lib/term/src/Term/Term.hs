{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
  -- for ByteString
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
--
-- Term Algebra and related notions.
module Term.Term (

    -- ** Pretty printing and query functions.
      prettyTerm
    , showFunSymName
    , lits

    -- ** Smart constructors
    , fAppOne
    , fAppZero
    , fAppDHNeutral
    , fAppDiff
    , fAppExp
    , fAppInv
    , fAppPMult
    , fAppEMap
    , fAppUnion
    , fAppPair
    , fAppFst
    , fAppSnd
    , fAppNatOne
    , fAppHomEnc
    , fAppHomDec

    -- ** Destructors and classifiers
    , isPair
    , isFst
    , isSnd
    , isDiff
    , isInverse
    , isProduct
    , isXor
    , isHomEnc
    , isHomDec
    , hasSameHomKey
    , isAnyHom
    , isUnion
    , isEMap
    , isNullaryPublicFunction
    , isPrivateFunction
    , isAC
    , isACC
    , getLeftTerm
    , getRightTerm
    , hasAny

    -- ** "Protected" subterms
    , allProtSubterms
    , elemNotBelowReducible

    -- * AC, C, and NonAC funcion symbols
    , FunSym(..)
    , ACSym(..)
    , CSym(..)
    , Privacy(..)
    , Constructability(..)
    , NoEqSym

    -- ** Signatures
    , FunSig
    , NoEqFunSig

    -- ** concrete symbols strings
    , diffSymString
    , munSymString 
    , expSymString
    , invSymString
    , pmultSymString
    , emapSymString
    , unionSymString
    , natPlusSymString
    , natOneSymString
    , oneSymString
    , dhNeutralSymString
    , multSymString
    , zeroSymString
    , xorSymString
    , homEncSymString
    , homDecSymString

    -- ** Function symbols
    , diffSym
    , expSym
    , pmultSym
    , natOneSym
    , oneSym
    , zeroSym
    , dhNeutralSym

    -- ** concrete signatures
    , dhFunSig
    , bpFunSig
    , msetFunSig
    , natFunSig
    , xorFunSig
    , homFunSig
    , pairFunSig
    , pairFunDestSig    
    , dhReducibleFunSig
    , bpReducibleFunSig
    , xorReducibleFunSig
    , homReducibleFunSig
    , homEncFunSig
    , implicitFunSig

    , module Term.Term.Classes
    , module Term.Term.Raw
    ) where

-- import           Data.Monoid
-- import           Data.Foldable (foldMap)

import qualified Data.Set as S
import qualified Data.ByteString.Char8 as BC
import           Extension.Data.ByteString ()

import           Text.PrettyPrint.Class

import           Term.Term.Classes
import           Term.Term.FunctionSymbols
import           Term.Term.Raw

----------------------------------------------------------------------
-- Smart Constructors
----------------------------------------------------------------------

-- | Smart constructors for one, zero.
fAppOne :: Term a
fAppOne = fAppNoEq oneSym []

fAppDHNeutral :: Term a
fAppDHNeutral = fAppNoEq dhNeutralSym []

fAppZero :: Term a
fAppZero = fAppNoEq zeroSym []

-- | Smart constructors for one on naturals.
fAppNatOne :: Term a
fAppNatOne  = fAppNoEq natOneSym []

-- | Smart constructors for diff, pair, exp, pmult, and emap.
fAppDiff, fAppPair, fAppExp, fAppPMult :: (Term a, Term a) -> Term a
fAppDiff (x,y)  = fAppNoEq diffSym  [x, y]
fAppPair (x,y)  = fAppNoEq pairSym  [x, y]
fAppExp  (b,e)  = fAppNoEq expSym   [b, e]
fAppPMult (s,p) = fAppNoEq pmultSym [s, p]
fAppEMap,fAppUnion :: Ord a => (Term a, Term a) -> Term a
fAppEMap  (x,y) = fAppC    EMap     [x, y]
fAppUnion (x,y) = fAppAC    Union     [x, y]

-- | Smart constructors for inv, fst, and snd.
fAppInv, fAppFst, fAppSnd :: Term a -> Term a
fAppInv e = fAppNoEq invSym [e]
fAppFst a = fAppNoEq fstSym [a]
fAppSnd a = fAppNoEq sndSym [a]

-- | Smart constructor for homomorphic encryption and decryption.
fAppHomEnc, fAppHomDec :: (Term a, Term a) -> Term a
fAppHomEnc (x, y) = fAppNoEq homEncSym [x, y]
fAppHomDec (x, y) = fAppNoEq homDecSym [x, y]

-- | @lits t@ returns all literals that occur in term @t@. List can contain duplicates.
lits :: Term a -> [a]
lits = foldMap return

----------------------------------------------------------------------
-- Classifiers
----------------------------------------------------------------------

-- | 'True' iff the term is a well-formed pair.
isPair :: Show a => Term a -> Bool
isPair (viewTerm2 -> FPair _ _) = True
isPair _                        = False

-- | 'True' iff the term is a fst function.
isFst :: Show a => Term a -> Bool
isFst (viewTerm -> FApp (NoEq sym) [_]) = sym == fstSym
isFst _                               = False

-- | 'True' iff the term is a snd function.
isSnd :: Show a => Term a -> Bool
isSnd (viewTerm -> FApp (NoEq sym) [_]) = sym == sndSym
isSnd _                               = False

-- | 'True' iff the term is a well-formed diff term.
isDiff :: Show a => Term a -> Bool
isDiff (viewTerm2 -> FDiff _ _) = True
isDiff _                        = False

-- | 'True' iff the term is a well-formed inverse.
isInverse :: Show a => Term a -> Bool
isInverse (viewTerm2 -> FInv _) = True
isInverse _                     = False

-- | 'True' iff the term is a well-formed product.
isProduct :: Show a => Term a -> Bool
isProduct (viewTerm2 -> FMult _) = True
isProduct _                      = False

-- | 'True' iff the term is a well-formed xor.
isXor :: Show a => Term a -> Bool
isXor (viewTerm2 -> FXor _) = True
isXor _                     = False

-- | 'True' iff the term is a well-form homomorphic encryption.
isHomEnc :: Show a => Term a -> Bool
isHomEnc (viewTerm2 -> FHenc _ _) = True
isHomEnc _                        = False

-- | 'True' iff the term is a well-form homomorphic encryption.
isHomDec :: Show a => Term a -> Bool
isHomDec (viewTerm2 -> FHdec _ _) = True
isHomDec _                        = False

hasSameHomKey :: (Eq a, Show a) => Term a -> Term a -> Bool
hasSameHomKey t1 t2 = case (viewTerm2 t1, viewTerm2 t2) of
  (FHenc _ k1, FHenc _ k2) -> k1 == k2
  (FHenc _ k1, FHdec _ k2) -> k1 == k2
  (FHdec _ k1, FHenc _ k2) -> k1 == k2
  (FHdec _ k1, FHdec _ k2) -> k1 == k2
  (_, _) -> False

isAnyHom :: Show a => Term a -> Bool
isAnyHom t = isHomEnc t || isHomDec t

-- | 'True' iff the term is a well-formed emap.
isEMap :: Show a => Term a -> Bool
isEMap (viewTerm2 -> FEMap _ _) = True
isEMap _                        = False

-- | 'True' iff the term is a well-formed union.
isUnion :: Show a => Term a -> Bool
isUnion (viewTerm2 -> FUnion _) = True
isUnion _                       = False

-- | 'True' iff the term is a nullary, public function.
isNullaryPublicFunction :: Term a -> Bool
isNullaryPublicFunction (viewTerm -> FApp (NoEq (_, (0, Public,_))) _) = True
isNullaryPublicFunction _                                            = False

isPrivateFunction :: Term a -> Bool
isPrivateFunction (viewTerm -> FApp (NoEq (_, (_,Private,_))) _) = True
isPrivateFunction _                                            = False

-- | 'True' iff the term is an AC-operator.
isAC :: Show a => Term a -> Bool
isAC (viewTerm -> FApp (AC _) _) = True
isAC _                           = False

-- | 'True' iff the term is an AC-operator or a C-operator.
isACC :: Show a => Term a -> Bool
isACC (viewTerm -> FApp (AC _) _) = True
isACC (viewTerm -> FApp (C  _) _) = True
isACC _                           = False

-- | 'True' iff the function applied to the term itself or any subterm returns 'True'
hasAny :: Show a => (Term a -> Bool) -> Term a -> Bool 
hasAny f t = case viewTerm t of
  Lit _              -> f t
  FApp _ args        -> f t || any (hasAny f) args

----------------------------------------------------------------------
-- Convert Diff Terms
----------------------------------------------------------------------

getSide :: DiffType -> Term a -> Term a
getSide _  (LIT l) = LIT l
getSide dt (FAPP (NoEq o) [t1,t2]) = case dt of
    DiffLeft  | o == diffSym -> getSide dt t1
    DiffRight | o == diffSym -> getSide dt t2
    DiffBoth  | o == diffSym -> FAPP (NoEq o) [(getSide dt t1),(getSide dt t2)]
    DiffNone  | o == diffSym -> error $ "getSide: illegal use of diff"
    _                        -> FAPP (NoEq o) [(getSide dt t1),(getSide dt t2)]
getSide dt (FAPP sym ts) = FAPP sym (map (getSide dt) ts)

getLeftTerm :: Term a -> Term a
getLeftTerm t = getSide DiffLeft t

getRightTerm :: Term a -> Term a
getRightTerm t = getSide DiffRight t

----------------------------------------------------------------------
-- "protected" subterms
-- NB: here anything but a pair or an AC symbol is protected!
----------------------------------------------------------------------

-- | Given a term, compute all protected subterms, i.e. all terms
-- which top symbol is a function, but not a pair, nor an AC symbol
allProtSubterms :: Show a => Term a -> [Term a]
allProtSubterms t@(viewTerm -> FApp _ as) | isPair t || isAC t
        = concatMap allProtSubterms as
allProtSubterms t@(viewTerm -> FApp _ as) | otherwise
        = t:concatMap allProtSubterms as
allProtSubterms _                                     = []

-- | Is term @inner@ in term @outer@ and not below a reducible function symbol?
-- This is used for the Subterm relation
elemNotBelowReducible :: Eq a => FunSig -> Term a -> Term a -> Bool
elemNotBelowReducible _ inner outer
                      | inner == outer = True
elemNotBelowReducible reducible inner (viewTerm -> FApp f as)
                      | f `S.notMember` reducible
                            = any (elemNotBelowReducible reducible inner) as
elemNotBelowReducible _ _ _ = False

----------------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------------

-- | Convert a function symbol to its name.
showFunSymName :: FunSym -> String
showFunSymName (NoEq (bs, _)) = BC.unpack bs
showFunSymName (AC op)        = show op
showFunSymName (C op )           = show op
showFunSymName List              = "List"

-- | Pretty print a term.
prettyTerm :: (Document d, Show l) => (l -> d) -> Term l -> d
prettyTerm ppLit = ppTerm
  where
    ppTerm t = case viewTerm t of
        Lit l                                     -> ppLit l
        FApp (AC o)            ts                 -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)   [t1,t2] | s == expSym     -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)   [t1,t2] | s == diffSym    -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq s)   []      | s == natOneSym  -> text "%1"
        FApp (NoEq s)   _       | s == pairSym    -> ppTerms ", " 1 "<" ">" (split t)
        FApp (NoEq (f, _)) []                     -> text (BC.unpack f)
        FApp (NoEq (f, _)) ts                     -> ppFun f ts
        FApp (C EMap)      ts                     -> ppFun emapSymString ts
        FApp List          ts                     -> ppFun "LIST" ts

    ppACOp Mult    = "*"
    ppACOp Xor     = "⊕"
    ppACOp Union   = "++"
    ppACOp NatPlus = "%+"
 
    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) .
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts

    split (viewTerm2 -> FPair t1 t2) = t1 : split t2
    split t                          = [t]

    ppFun f ts =
        text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
