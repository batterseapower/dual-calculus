module Syntax where

import Control.Arrow ( first, second, (&&&), (***) )

import Data.Unique.Id
import Data.Maybe
import Debug.Trace

import System.IO.Unsafe

import Text.PrettyPrint.HughesPJClass


type Var = String
type CoVar = String

type Constructor = String

data Term   = Var Var     | Data Constructor Term                | Tup [Term]       | Not CoTerm | Lam Var Term      | Bind Stmt CoVar | Fix Var Term
data CoTerm = CoVar CoVar | CoData [(Maybe Constructor, CoTerm)] | CoTup Int CoTerm | CoNot Term | CoLam Term CoTerm | CoBind Var Stmt -- | CoFix CoTerm CoVar
data Stmt   = Term `Cut` CoTerm

type Bind = (Var, Term)
type CoBind = (CoVar, CoTerm)


dot = text "."

instance Pretty Term where
    pPrintPrec level prec m = case m of
        Var x      -> text x
        Data con m -> prettyParen (prec >= 9) (text con <+> pPrintPrec level 9 m)
        Tup ms     -> parens $ fsep $ punctuate comma $ map (pPrintPrec level 0) ms
        Not k      -> brackets (pPrintPrec level 0 k) <> text "~"
        Lam x m    -> prettyParen (prec >= 9) (text "\\" <> text x <> dot <+> pPrintPrec level 0 m)
        Bind s a   -> parens (pPrintPrec level 0 s) <> dot <> text a
        Fix x m    -> text "fix" <+> text x <> dot <> parens (pPrintPrec level 0 m)

instance Pretty CoTerm where
    pPrintPrec level prec k = case k of
        CoVar a     -> text a
        CoData alts -> hang (text "case") 2 (vcat [hang (maybe (text "_") text mb_con <+> text "->") 2 (pPrintPrec level 0 k) | (mb_con, k) <- alts])
        CoTup i k   -> int i <+> text "!!" <+> pPrintPrec level 0 k
        CoNot m     -> text "~" <> parens (pPrintPrec level 0 m)
        CoLam m k   -> prettyParen (prec >= 9) (pPrintPrec level 0 m <+> text "@" <+> pPrintPrec level 0 k)
        CoBind x s  -> text x <> dot <> parens (pPrintPrec level 0 s)

instance Pretty Stmt where
    pPrintPrec level prec k = case k of
        m `Cut` k      -> prettyParen (prec >= 9) (pPrintPrec level 9 m <+> text "●" <+> pPrintPrec level 9 k)


bindMany :: [(Var, Term)] -> Stmt -> Stmt
bindMany []            s = s
bindMany ((x, m):rest) s = m `Cut` CoBind x (bindMany rest s)

 -- CBV Is Dual To CBN, Reloaded: Section 3, Proposition 4
 -- NB: this is the call-by-name/need lambda abstraction, since I'm going to assume that reduction strategy in the supercompiler
lam_prims x m = Bind (Data "Left" (Not (CoBind x (Data "Right" m `Cut` CoVar alpha))) `Cut` CoVar alpha) alpha
colam_prims m k = CoData [(Just "Left", CoNot m), (Just "Right", k)]
app_prims m n = Bind (m `Cut` (n `colam_prims` CoVar alpha)) alpha

lam = Lam
colam = CoLam

app m n = Bind (m `Cut` (n `colam` CoVar alpha)) alpha
letin x m n = Bind (m `Cut` (CoBind x (n `Cut` CoVar alpha))) alpha
letrecin x m n = Bind (Fix x m `Cut` (CoBind x (n `Cut` CoVar alpha))) alpha


{-# NOINLINE wildIdSupply #-}
wildIdSupply :: IdSupply
wildIdSupply = unsafePerformIO $ initIdSupply 'a'

alpha, ecks :: String
(alpha:ecks:_) = map anyVarName $ splitIdSupplyL wildIdSupply

anyVarName :: IdSupply -> String
anyVarName = show . idFromSupply
