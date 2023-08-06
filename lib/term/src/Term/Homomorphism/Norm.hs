module Term.Homomorphism.Norm (
  normHomomorphic
) where

import Term.LTerm (
  LNTerm, isPair, fAppPair,
  TermView(FApp), viewTerm, termViewToTerm)

import Term.Homomorphism.LNPETerm

-- | @normHomomorphic t@ normalizes the term @t@ if the top function is the homomorphic encryption
normHomomorphic :: LNTerm -> LNTerm
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