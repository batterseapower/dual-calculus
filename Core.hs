module Core where

import Syntax

import Data.Unique.Id

import Text.PrettyPrint.HughesPJClass


data Core = CoreVar Var
          | CoreLam Var Core
          | CoreApp Core Core
          | CoreLet Var Core Core
          | CoreLetRec Var Core Core
          | CoreCase Core (Var, Core) (Var, Core)
          | CoreSelect Core FstSnd Var Core

instance Pretty Core where
    pPrintPrec level prec t = case t of
        CoreVar x                    -> text x
        CoreLam x t                  -> prettyParen (prec >= 9) (lambda <> text x <> dot <+> pPrintPrec level 0 t)
        CoreApp t1 t2                -> prettyParen (prec >= 9) (pPrintPrec level 0 t1 <+> pPrintPrec level 9 t2)
        CoreLet x t1 t2              -> prettyParen (prec >= 9) (text "let"    <+> text x <+> equals <+> pPrintPrec level 0 t1 $$ text "in" <+> pPrintPrec level 0 t2)
        CoreLetRec x t1 t2           -> prettyParen (prec >= 9) (text "letrec" <+> text x <+> equals <+> pPrintPrec level 0 t1 $$ text "in" <+> pPrintPrec level 0 t2)
        CoreCase t (x1, t1) (x2, t2) -> prettyParen (prec >= 9) (text "case" <+> pPrintPrec level 0 t <+> text "of" $$ nest 2 (alt Inl x1 t1 $$ alt Inr x2 t2))
          where alt lr x t = hang (pPrint lr <+> text x <+> text "->") 2 (pPrintPrec level 0 t)
        CoreSelect t1 fs x t2        -> prettyParen (prec >= 9) (hang (text "select" <+> pPrintPrec level 0 t1 <+> text "!!" <+> pPrint fs <+> text x <+> text "->") 2 (pPrintPrec level 0 t2))


-- Investigations on the Dual Calculus, Nikos Tzevelekos: Definition 1.6, p7
dualize :: IdSupply -> Core -> Term
dualize _   (CoreVar x) = Var x
dualize ids (CoreLam x t) = Lam x (dualize ids t)
dualize ids (CoreApp t1 t2) = Bind (dualize ids2 t1 `Cut` (dualize ids3 t2 `CoLam` CoVar a)) a
  where (ids1, ids') = splitIdSupply ids
        (ids2, ids3) = splitIdSupply ids'
        a = "$a" ++ show (idFromSupply ids1)
dualize ids (CoreLet v t1 t2) = letin v (dualize ids1 t1) (dualize ids2 t2)
  where (ids1, ids2) = splitIdSupply ids
dualize ids (CoreLetRec v t1 t2) = letrecin v (dualize ids1 t1) (dualize ids2 t2)
  where (ids1, ids2) = splitIdSupply ids
dualize ids (CoreCase t (y1, t1) (y2, t2)) = Bind (dualize ids2 t `Cut` CoData (CoBind y1 (dualize ids3 t1 `Cut` CoVar a)) (CoBind y2 (dualize ids4 t2 `Cut` CoVar a))) a
  where ids1:ids2:ids3:ids4:_ = splitIdSupplyL ids
        a = "$a" ++ show (idFromSupply ids1)
dualize ids (CoreSelect t1 fs v t2) = Bind (dualize ids2 t1 `Cut` CoTup fs (CoBind v $ dualize ids3 t2 `Cut` CoVar a)) a
  where (ids1, ids') = splitIdSupply ids
        (ids2, ids3) = splitIdSupply ids'
        a = "$a" ++ show (idFromSupply ids1)

{-
cpsTerm :: Term -> LamTerm
cpsTerm =

data PendingTerm = AdminTerm (LamTerm -> LamTerm)
                 | ResidTerm LamTerm

applyTerm :: PendingTerm -> LamTerm -> LamTerm
applyTerm (ResidTerm t1) t2 = App t1 t2
applyTerm (AdminTerm f)  t2 = f t2

cpsCoTerm :: CoTerm -> PendingTerm -> LamTerm
cpsCoTerm k pt = case k of
    CoVar a     -> applyTerm pt (LamVar a)
    {-
    CoData alts -> foldr go (\k -> f (mkTup bs)) (alts `zip` bs)
      where go ((mb_con, k), b) f = \k -> cpsCoTerm k f
            bs = ...
    -}
    CoTup i k   -> cpsCoTerm k (\k -> )
    CoLam m k   ->
    CoBind x s  -> 

cpsStmt :: Stmt -> LamTerm
cpsStmt (m `Cut` k) = cpsCoTerm k (cpsTerm m)
-}

{-
example1 = letrecin (Var "map") (lam "f" $ lam "xs" $ Bind (Var "xs" `Cut` CoData [(Just "Nil", CoBind "_" (Data "Nil" (Tup []) `Cut` CoVar "a")),
                                                                                   (Just "Cons", CoBind "cons" (CoVar "cons" `Cut` CoBind "y" (CoVar "cons" `Cut` CoBind "ys" (
                                                                                       Data "Cons" (Tup [app (Var "f") (Var "x"), app (app (Var "map") (Var "f")) (Var "map")]) `Cut` CoVar "a"))))]) "a")
                    (app (app (Var "map") (Var "inc")) $ app (app (Var "map") (Var "double")) (Var "input"))
-}
