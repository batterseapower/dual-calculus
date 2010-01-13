module Syntax where

import Data.Unique.Id

import System.IO.Unsafe

import Text.PrettyPrint.HughesPJClass


type Var = String
type CoVar = String

data InlInr = Inl | Inr deriving (Eq)
data FstSnd = Fst | Snd deriving (Eq)

data Term   = Var Var     | Data Term InlInr      | Tup Term Term       | Not CoTerm | Lam Var Term      | Bind Stmt CoVar | Fix Var Term             deriving (Eq)
data CoTerm = CoVar CoVar | CoData CoTerm CoTerm  | CoTup FstSnd CoTerm | CoNot Term | CoLam Term CoTerm | CoBind Var Stmt {- | CoFix CoTerm CoVar -} deriving (Eq)
data Stmt   = Term `Cut` CoTerm deriving (Eq)

type Bind = (Var, Term)
type CoBind = (CoVar, CoTerm)


-- Note [Lambdas]
-- ~~~~~~~~~~~~~~
--
-- Lambdas and colambdas are strictly speaking unnecessary, because you can always encode them away by using a
-- evaluation-strategy specific means. However, they are sure as hell easier to read than their encodings!
--
-- If we avoid using the encoding, you can drop Not and CoNot when compiling a language without first class
-- continuations.

-- Note [Fixpoints]
-- ~~~~~~~~~~~~~~~~
--
-- Because I allow recursive data with contravariant occurences, the fixed point operators can be
-- encoded away, analagously to how you can encode away lambdas and applications. The encoding
-- of fix is as follows:
--   fix x. M = ((\u. (u ● case MkU -> p.((p ● u @ c).c ● x.(M ● b))).b) ● russel.(russel ● (MkU russel @ a))).a
--
-- Where we have:
--   data U a = MkU (U a -> a)
--
-- Note that we *might* be able to clean up this combinator a bit if we expanded the definition of lambda and @,
-- and then reduced.
--
-- One issue with this combinator is that it doesn't preserve sharing of M in call by need.


dot = text "."
dnot = text "not"
at = text "@"
cut = text "●"
lambda = text "\\"
fix = text "fix"
angles d = text "<" <> d <> text ">"

instance Show InlInr where show = show . pPrint

instance Pretty InlInr where
    pPrint Inl = text "inl"
    pPrint Inr = text "inr"

instance Show FstSnd where show = show . pPrint

instance Pretty FstSnd where
    pPrint Fst = text "fst"
    pPrint Snd = text "snd"

instance Show Term where show = show . pPrint

instance Pretty Term where
    pPrintPrec level prec m = case m of
        Var x     -> text x
        Data m lr -> angles (pPrintPrec level 0 m) <> pPrint lr
        Tup m n   -> parens $ pPrintPrec level 0 m <> comma <+> pPrintPrec level 0 n
        Not k     -> brackets (pPrintPrec level 0 k) <> dnot
        Lam x m   -> prettyParen (prec >= 9) (lambda <> text x <> dot <+> pPrintPrec level 0 m)
        Bind s a  -> parens (pPrintPrec level 0 s) <> dot <> text a
        Fix x m   -> fix <+> text x <> dot <> parens (pPrintPrec level 0 m)

instance Show CoTerm where show = show . pPrint

instance Pretty CoTerm where
    pPrintPrec level prec k = case k of
        CoVar a    -> text a
        CoData k l -> brackets (pPrintPrec level 0 k <> comma <+> pPrintPrec level 0 l)
        CoTup fs k -> pPrint fs <> brackets (pPrintPrec level 0 k)
        CoNot m    -> dnot <> parens (pPrintPrec level 0 m)
        CoLam m k  -> prettyParen (prec >= 9) (pPrintPrec level 0 m <+> at <+> pPrintPrec level 0 k)
        CoBind x s -> text x <> dot <> parens (pPrintPrec level 0 s)

instance Show Stmt where show = show . pPrint

instance Pretty Stmt where
    pPrintPrec level prec k = case k of
        m `Cut` k -> prettyParen (prec >= 9) (pPrintPrec level 9 m <+> cut <+> pPrintPrec level 9 k)


app m n = Bind (m `Cut` (n `CoLam` CoVar wildAlpha)) wildAlpha
letin x m n = Bind (m `Cut` (CoBind x (n `Cut` CoVar wildAlpha))) wildAlpha
letrecin x m n = Bind (Fix x m `Cut` (CoBind x (n `Cut` CoVar wildAlpha))) wildAlpha

bindMany :: [(Var, Term)] -> Stmt -> Stmt
bindMany binds s = foldr (\(x, m) s -> m `Cut` CoBind x s) s binds


{-# NOINLINE wildIdSupply #-}
wildIdSupply :: IdSupply
wildIdSupply = unsafePerformIO $ initIdSupply 'a'

wildAlpha, wildEcks :: String
(wildAlpha:wildEcks:_) = map (show . idFromSupply) $ splitIdSupplyL wildIdSupply
