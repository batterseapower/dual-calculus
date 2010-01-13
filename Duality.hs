module Duality( dualizeStmt, dualizeTerm, dualizeCoTerm ) where

import Syntax


dualizeStmt :: Stmt -> Stmt
dualizeStmt (m `Cut` k) = dualizeCoTerm k `Cut` dualizeTerm m

dualizeTerm :: Term -> CoTerm
dualizeTerm (Var x) = CoVar x
dualizeTerm (Tup m n) = CoData (dualizeTerm m) (dualizeTerm n)
dualizeTerm (Data m lr) = CoTup (case lr of Inl -> Fst; Inr -> Snd) (dualizeTerm m)
dualizeTerm (Not k) = CoNot (dualizeCoTerm k)
dualizeTerm (Bind s a) = CoBind a (dualizeStmt s)

dualizeCoTerm :: CoTerm -> Term
dualizeCoTerm (CoVar a) = Var a
dualizeCoTerm (CoData k l) = Tup (dualizeCoTerm k) (dualizeCoTerm l)
dualizeCoTerm (CoTup fs k) = Data (dualizeCoTerm k) (case fs of Fst -> Inl; Snd -> Inr)
dualizeCoTerm (CoNot m) = Not (dualizeTerm m)
dualizeCoTerm (CoBind x s) = Bind (dualizeStmt s) x
