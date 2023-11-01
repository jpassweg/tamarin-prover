{-# LANGUAGE DeriveDataTypeable #-}

module Term.Homomorphism.MConst (
    MConst(..)
  , toMConstA
  , toMConstC
  , toMConstVarList
  , fromMConst
  , sortOfMConst
) where

-- For data MConst
import Data.Typeable ( Typeable )
import Data.Data ( Data )

import Term.LTerm (LTerm, Lit(Var, Con), IsConst, LVar(..), TermView(FApp, Lit), LSort(..), viewTerm, termViewToTerm)
-- Lit(Var, Con), IsConst, isVar, varTerm, termVar, varsVTerm, occursVTerm come from Term.VTerm
-- isHomEnc come from Term.Term
-- TermView(Lit, FApp), viewTerm, termViewToTerm come from Term.Term.Raw

-- Const type used by matching algorithm
data MConst c = MCon c | MVar LVar
  deriving (Eq, Ord, Show, Data, Typeable)

instance (Ord c, Eq c, Show c, Data c, IsConst c) => IsConst (MConst c) where

toMConstA :: IsConst c => LTerm c -> LTerm (MConst c)
toMConstA t = case viewTerm t of
  (FApp funsym args) -> termViewToTerm (FApp funsym $ map toMConstA args)
  (Lit (Var v))      -> termViewToTerm (Lit (Con (MVar v)))
  (Lit (Con c))      -> termViewToTerm (Lit (Con (MCon c)))

toMConstC :: IsConst c => LTerm c -> LTerm (MConst c)
toMConstC t = case viewTerm t of
  (FApp funsym args) -> termViewToTerm (FApp funsym $ map toMConstC args)
  (Lit (Var v))      -> termViewToTerm (Lit (Var v))
  (Lit (Con c))      -> termViewToTerm (Lit (Con (MCon c)))

toMConstVarList :: IsConst c => [LVar] -> LTerm c -> LTerm (MConst c)
toMConstVarList vars t = case viewTerm t of
  (FApp funsym args) -> termViewToTerm (FApp funsym $ map toMConstC args)
  (Lit (Var v))      -> if v `elem ` vars 
                        then termViewToTerm (Lit (Con (MVar v)))
                        else termViewToTerm (Lit (Var v))
  (Lit (Con c))      -> termViewToTerm (Lit (Con (MCon c)))  

fromMConst :: IsConst c => LTerm (MConst c) -> LTerm c
fromMConst t = case viewTerm t of
  (FApp funsym args)   -> termViewToTerm (FApp funsym $ map fromMConst args)
  (Lit (Var v))        -> termViewToTerm (Lit (Var v))
  (Lit (Con (MCon c))) -> termViewToTerm (Lit (Con c))
  (Lit (Con (MVar v))) -> termViewToTerm (Lit (Var v))

 -- con of nodes are messages somehow
sortOfMConst :: IsConst c => (c -> LSort) -> MConst c -> LSort
sortOfMConst sortOf (MCon c) = sortOf c
sortOfMConst _      (MVar v) = lvarSort v