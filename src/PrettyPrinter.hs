module PrettyPrinter
  ( printTerm
  ,     -- pretty printer para terminos
    printType     -- pretty printer para tipos
  )
where

import           Common
import           Text.PrettyPrint.HughesPJ
import           Prelude                 hiding ( (<>) )
-- lista de posibles nombres para variables
vars :: [String]
vars =
  [ c : n
  | n <- "" : map show [(1 :: Integer) ..]
  , c <- ['x', 'y', 'z'] ++ ['a' .. 'w']
  ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-- pretty-printer de términos

pp :: Int -> [String] -> Term -> Doc
pp ii vs Unit              = text "unit"
pp ii vs (Bound k         ) = text (vs !! (ii - k - 1))
pp _  _  (Free  (Global s)) = text s
pp ii vs (Let t1 t2       ) =
    sep [text "let", text (vs !! ii), text "=", pp ii vs t1, text "in", pp (ii + 1) vs t2]
pp ii vs (i :@: c         ) = sep
  [ parensIf (isLam i) (pp ii vs i)
  , nest 1 (parensIf (isLam c || isApp c) (pp ii vs c))
  ]
pp ii vs (Lam t c) =
  text "\\"
    <> text (vs !! ii)
    <> text ":"
    <> printType t
    <> text ". "
    <> pp (ii + 1) vs c
pp ii vs (Pair t1 t2) =
  text "(" 
    <> pp ii vs t1
    <> text ","
    <> pp ii vs t2
    <> text ")"
pp ii vs (Fst t) = text "fst " <> pp ii vs t
pp ii vs (Snd t) = text "snd " <> pp ii vs t
pp ii vs 0 = text "0"
pp ii vs (Suc t)  = text "suc " <> pp ii vs t  
pp ii vs (R t1 t2 t3)  = sep [text "R", pp ii vs t1,
                              pp ii vs t2, pp ii vs t3] 


isLam :: Term -> Bool
isLam (Lam _ _) = True
isLam _         = False

isApp :: Term -> Bool
isApp (_ :@: _) = True
isApp _         = False

isPair :: Term -> Bool
isPair (Pair _ _) = True
isPair _          = False

-- pretty-printer de tipos
printType :: Type -> Doc
printType EmptyT = text "E"
printType UnitT  = text "Unit"
printType NatT   = text "Nat"
printType (FunT t1 t2) =
  sep [parensIf (isFun t1) (printType t1), text "->", printType t2]
printType (PairT t1 t2) = 
  text "(" <> sep [printType t1, text ",", printType t2] <> text ")"


isFun :: Type -> Bool
isFun (FunT _ _) = True
isFun _          = False

fv :: Term -> [String]
fv (Bound _         ) = []
fv Unit               = []
fv Zero               = []
fv (Free  (Global n)) = [n]
fv (t   :@: u       ) = fv t ++ fv u
fv (Lam _   u       ) = fv u
fv (Let t1 t2)        = fv t1 ++ fv t2
fv (Pair t1 t2)       = fv t1 ++ fv t2
fv (Fst t)            = fv t
fv (Snd t)            = fv t
fv (Suc t)            = fv t
fv (Rec t1 t2 t3)     = fv t1 ++ fv t2 ++ fv t3

---
printTerm :: Term -> Doc
printTerm t = pp 0 (filter (\v -> not $ elem v (fv t)) vars) t

