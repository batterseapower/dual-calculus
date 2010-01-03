module Syntax where

import Data.Unique.Id

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
        m `Cut` k -> prettyParen (prec >= 9) (pPrintPrec level 9 m <+> text "●" <+> pPrintPrec level 9 k)


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
