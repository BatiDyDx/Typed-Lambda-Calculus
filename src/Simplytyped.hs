module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion = conversion' []

conversion' :: [String] -> LamTerm -> Term
conversion' b LUnit           = Unit
conversion' b (LVar n    )    = maybe (Free (Global n)) Bound (n `elemIndex` b)
conversion' b (LApp t u  )    = conversion' b t :@: conversion' b u
conversion' b (LAbs n t u)    = Lam t (conversion' (n : b) u)
conversion' b (LLet x t1 t2)  = Let (conversion' b t1) (conversion' (x:b) t2)
conversion' b (LPair t1 t2)   = Pair (conversion' b t1) (conversion' b t2)
conversion' b (LFst t)        = Fst (conversion' b t)
conversion' b (LSnd t)        = Snd (conversion' b t)
conversion' b LZero           = Zero
conversion' b (LSuc t)        = Suc (conversion' b t)
conversion' b (LRec t1 t2 t3) = Rec (conversion' b t1) (conversion' b t2) (conversion' b t3) 

-----------------------
--- eval
-----------------------

sub :: Int -> Term -> Term -> Term
sub i t Unit                  = Unit
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Lam t'  u)           = Lam t' (sub (i + 1) t u)
sub i t (Let t1 t2)           = let t1' = sub i t t1
                                    t2' = sub (i+1) t t2
                                in Let t1' t2'
sub i t (Pair t1 t2)          = let t1' = sub i t t1
                                    t2' = sub i t t2
                                in Pair t1' t2'
sub i t (Fst t1)              = Fst (sub i t t1)
sub i t (Snd t1)              = Snd (sub i t t1)
sub i t Zero                  = Zero
sub i t (Suc t1)              = Suc (sub i t t1)
sub i t (Rec t1 t2 t3)        = let t1' = sub i t t1
                                    t2' = sub i t t2
                                    t3' = sub i t t3
                                in Rec t1' t2' t3'
--
-- evaluador de términos
eval :: NameEnv Value Type -> Term -> Value
eval e Unit                   = VUnit
eval _ (Bound _             ) = error "variable ligada inesperada en eval"
eval e (Free  n             ) = fst $ fromJust $ lookup n e
eval _ (Lam      t   u      ) = VLam t u
eval e (Lam _ u  :@: Lam s v) = eval e (sub 0 (Lam s v) u)
eval e (Lam t u1 :@: u2     ) = let v2 = eval e u2 in eval e (sub 0 (quote v2) u1)
eval e (u        :@: v      ) = case eval e u of
  VLam t u' -> eval e (Lam t u' :@: v)
  _         -> error "Error de tipo en run-time, verificar type checker"
eval e (Let t1 t2           ) = let v = eval e t1 in eval e (sub 0 (quote v) t2) 
eval e (Pair t1 t2          ) = let v1 = eval e t1
                                    v2 = eval e t2
                                in VPair v1 v2
eval e (Fst t               ) = case eval e t of
  VPair v1 v2 -> v1
  _           -> error "Error de tipo en run-time, verificar type checker"
eval e (Snd t               ) = case eval e t of
  VPair v1 v2 -> v2
  _           -> error "Error de tipo en run-time, verificar type checker"
eval e Zero                   = VNum NZero  
eval e (Suc t)                = case eval e t of
                                  VNum v -> VNum $ NSuc $ v
                                  _      -> error "error"
eval e (Rec t1 t2 Zero      ) = eval e t1
eval e (Rec t1 t2 (Suc t3)  ) = eval e ((t2 :@: (Rec t1 t2 t3)) :@: t3)
eval e (Rec t1 t2 t3)         = case eval e t3 of
                                   VNum v -> eval e (Rec t1 t2 (quoteNV v))
                                   -- VNum v -> eval e (unfoldRec t1 t2 v)
                                   _      -> error "Error de tipo en run-time, verificar type checker"

unfoldRec :: Term -> Term -> NumVal -> Term
unfoldRec t1 t2 NZero = t1
unfoldRec t1 t2 (NSuc v) = (t2 :@: (unfoldRec t1 t2 v))

-----------------------
--- quoting
-----------------------
quoteNV :: NumVal -> Term
quoteNV NZero = Zero
quoteNV (NSuc v) = Suc (quoteNV v)

quote :: Value -> Term
quote (VLam t f) = Lam t f
quote VUnit      = Unit
quote (VNum v) = quoteNV v
quote (VPair v1 v2) = Pair (quote v1) (quote v2)

----------------------
--- type checker
-----------------------

-- type checker
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=)
  :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error

matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notpairError :: Type -> Either String Type
notpairError t1 = err $ render (printType t1) ++ " no es un par."

notnatError :: Type -> Either String Type
notnatError t1 = err $ render (printType t1) ++ " no es un natural."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free  n) = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u) = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt
infer' c e (Lam t u) = infer' (t : c) e u >>= \tu -> ret $ FunT t tu
infer' c e (Let t1 t2) = infer' c e t1 >>= \tu -> infer' (tu:c) e t2
infer' c e Unit  = ret $ UnitT
infer' c e (Pair t1 t2) = infer' c e t1 >>= \tu1 -> infer' c e t2
                          >>= \tu2 -> ret $ PairT tu1 tu2
infer' c e (Fst t) = infer' c e t >>= \tt ->
  case tt of
    PairT tu1 tu2 -> ret tu1
    _             -> notpairError tt
infer' c e (Snd t) = infer' c e t >>= \tt ->
  case tt of
    PairT tu1 tu2 -> ret tu2
    _             -> notpairError tt
infer' c e Zero = ret NatT
infer' c e (Suc t) = infer' c e t >>= \tt ->
  case tt of
    NatT -> ret NatT
    _    -> notnatError tt
infer' c e (Rec t1 t2 t3) = do  tt1 <- infer' c e t1
                                tt2 <- infer' c e t2
                                tt3 <- infer' c e t3
                                if tt3 /= NatT
                                then notnatError tt3
                                else matchRecTypes tt1 tt2

matchRecTypes :: Type -> Type -> Either String Type
matchRecTypes t (FunT (FunT s n) r) | n /= NatT = matchError NatT n
                                    | t /= s    = matchError t s
                                    | s /= r    = matchError s r
                                    | otherwise = ret t
matchRecTypes _ (FunT s r) = notfunError s
matchRecTypes _ s          = notfunError s
----------------------------------
