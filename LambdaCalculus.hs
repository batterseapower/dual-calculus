module LambdaCalculus where

import Syntax

import Control.Arrow ( first, second, (&&&), (***) )

import Data.Unique.Id
import Data.Maybe
import Debug.Trace

import System.IO.Unsafe

import Text.PrettyPrint.HughesPJClass


data LamTerm = LamVar Var | LamLam Var LamTerm | App LamTerm LamTerm | Let Var LamTerm LamTerm | LetRec Var LamTerm LamTerm | Case LamTerm [(Maybe Constructor, [Var], LamTerm)]

instance Pretty LamTerm where
    pPrintPrec level prec t = case t of
        LamVar x       -> text x
        LamLam x t     -> prettyParen (prec >= 9) (text "\\" <> text x <> dot <+> pPrintPrec level 0 t)
        App t1 t2      -> prettyParen (prec >= 9) (pPrintPrec level 0 t1 <+> pPrintPrec level 9 t2)
        Let x t1 t2    -> prettyParen (prec >= 9) (text "let"    <+> text x <+> text "=" <+> pPrintPrec level 0 t1 $$ text "in" <+> pPrintPrec level 0 t2)
        LetRec x t1 t2 -> prettyParen (prec >= 9) (text "letrec" <+> text x <+> text "=" <+> pPrintPrec level 0 t1 $$ text "in" <+> pPrintPrec level 0 t2)
        Case t alts    -> prettyParen (prec >= 9) (text "case" <+> pPrintPrec level 0 t <+> text "of" $$ nest 2 (vcat $ [hang (maybe (text "_") text mb_con <+> text "->") 2 (pPrintPrec level 0 t) | (mb_con, bs, t) <- alts]))


-- Investigations on the Dual Calculus, Nikos Tzevelekos: Definition 1.6, p7
dualize :: IdSupply -> LamTerm -> Term
dualize ids (LamVar x) = Var x
dualize ids (LamLam x t)  = lam x (dualize ids t)
dualize ids (App t1 t2) = Bind (dualize ids2 t1 `Cut` (dualize ids3 t2 `colam` CoVar a)) a
  where (ids1, ids') = splitIdSupply ids
        (ids2, ids3) = splitIdSupply ids'
        a = "$a" ++ show (idFromSupply ids1)
dualize ids (Let v t1 t2) = letin v (dualize ids1 t1) (dualize ids2 t2)
  where (ids1, ids2) = splitIdSupply ids
dualize ids (LetRec v t1 t2) = letrecin v (dualize ids1 t1) (dualize ids2 t2)
  where (ids1, ids2) = splitIdSupply ids
dualize ids (Case t alts) = Bind (dualize ids3 t `Cut` CoData [(con, CoBind x (foldr bind_alt_bndr (dualize ids t `Cut` CoVar a) (bs `zip` [0..]))) | ((con, bs, t), ids) <- alts `zip` idss]) a
  where ids1:ids2:ids3:idss = splitIdSupplyL ids
        a = "$a" ++ show (idFromSupply ids1)
        x = "$x" ++ show (idFromSupply ids2)
        bind_alt_bndr (b, i) s = Var x `Cut` CoTup i (CoBind b s)

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
