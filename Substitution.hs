module Substitution where

import Syntax


-- FIXME: this is all so, so wrong. Must rename binders if we want to ensure no capture of FVs of thing being substituted
-- It will work if the FVs of the thing being substituted are all fresh

substTerm y n m = case m of
  Var x | x == y    -> n
        | otherwise -> Var x
  Data con m -> Data con (substTerm y n m)
  Tup ms -> Tup (map (substTerm y n) ms)
  Not k -> Not (substTermK y n k)
  Lam x m | x == y    -> Lam x m
          | otherwise -> Lam x (substTerm y n m)
  Bind s a -> Bind (substTermS y n s) a
  Fix x m | x == y    -> Fix x m
          | otherwise -> Fix x (substTerm y n m)

substTermK :: String -> Term -> CoTerm -> CoTerm
substTermK y n k = case k of
  CoVar a -> CoVar a
  CoData alts -> CoData [(mb_con, substTermK y n k) | (mb_con, k) <- alts]
  CoTup i k -> CoTup i (substTermK y n k)
  CoNot m -> CoNot (substTerm y n m)
  CoLam m k -> CoLam (substTerm y n m) (substTermK y n k)
  CoBind x s | x == y    -> CoBind x s
             | otherwise -> CoBind x (substTermS y n s)

substTermS y n (m `Cut` k) = {- trace (prettyShow (y, n, m, k)) $ -} substTerm y n m `Cut` substTermK y n k


substCoTerm b l k = case k of
  CoVar a | a == b    -> l
          | otherwise -> CoVar a
  CoData alts -> CoData [(mb_con, substCoTerm b l k) | (mb_con, k) <- alts]
  CoTup i k -> CoTup i (substCoTerm b l k)
  CoNot m -> CoNot (substCoTermM b l m)
  CoLam m k -> CoLam (substCoTermM b l m) (substCoTerm b l k)
  CoBind x s -> CoBind x (substCoTermS b l s)

substCoTermM b l m = case m of
  Var x -> Var x
  Data con m -> Data con (substCoTermM b l m)
  Tup ms -> Tup (map (substCoTermM b l) ms)
  Not k -> Not (substCoTerm b l k)
  Lam x m -> Lam x (substCoTermM b l m)
  Bind s a | a == b    -> Bind s a
           | otherwise -> Bind (substCoTermS b l s) a
  Fix x m -> Fix x (substCoTermM b l m)

substCoTermS b l (m `Cut` k) = substCoTermM b l m `Cut` substCoTerm b l k