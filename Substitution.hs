module Substitution where

import Syntax

import Control.Arrow (first, second)

import qualified Data.Map as M
import qualified Data.Set as S


type InScopeSet = (S.Set Var, S.Set CoVar)

emptyInScopeSet :: InScopeSet
emptyInScopeSet = (S.empty, S.empty)


extendInScopeSetVar :: InScopeSet -> Var -> InScopeSet
extendInScopeSetVar iss x = first (S.insert x) iss

extendInScopeSetCoVar :: InScopeSet -> CoVar -> InScopeSet
extendInScopeSetCoVar iss a = second (S.insert a) iss


data Subst = Subst {
    subst_terms   :: M.Map Var Term,
    subst_coterms :: M.Map CoVar CoTerm,
    subst_inscope :: InScopeSet
  }

emptySubst :: InScopeSet -> Subst
emptySubst iss = Subst M.empty M.empty iss

termSubst :: Var -> Term -> Subst
termSubst = extendSubstTerm (emptySubst emptyInScopeSet)

coTermSubst :: CoVar -> CoTerm -> Subst
coTermSubst = extendSubstCoTerm (emptySubst emptyInScopeSet)


extendSubstTerm :: Subst -> Var -> Term -> Subst
extendSubstTerm s x m = s { subst_terms = M.insert x m (subst_terms s) }

extendSubstCoTerm :: Subst -> CoVar -> CoTerm -> Subst
extendSubstCoTerm s a k = s { subst_coterms = M.insert a k (subst_coterms s) }

uniqAway :: String -> S.Set String -> String
uniqAway x iss = go 0
  where go n | x' `S.notMember` iss = x'
             | otherwise            = go (n + 1)
          where x' = x ++ show n

substAnyBinder :: (InScopeSet -> S.Set String) -> (InScopeSet -> S.Set String -> InScopeSet)
               -> (Subst -> M.Map String a) -> (Subst -> M.Map String a -> Subst)
               -> (String -> a)
               -> Subst -> String -> (Subst, String)
substAnyBinder get set get_map set_map inj s x = (s' { subst_inscope = set iss (S.insert x' my_iss) }, x')
  where
    iss = subst_inscope s
    my_iss = get iss
    (s', x') | x `S.member` my_iss
             , let x' = uniqAway x my_iss = (set_map s (M.insert x (inj x') (get_map s)), x')
             | otherwise                  = (set_map s (M.delete x (get_map s)),          x)

substBinder :: Subst -> Var -> (Subst, Var)
substBinder = substAnyBinder fst (\iss set -> (set, snd iss)) subst_terms (\s m -> s { subst_terms = m }) Var

substCoBinder :: Subst -> CoVar -> (Subst, CoVar)
substCoBinder = substAnyBinder snd (\iss set -> (fst iss, set)) subst_coterms (\s m -> s { subst_coterms = m }) CoVar

substVar :: Subst -> Var -> Term
substVar s x = M.findWithDefault (Var x) x (subst_terms s)

substCoVar :: Subst -> CoVar -> CoTerm
substCoVar s a = M.findWithDefault (CoVar a) a (subst_coterms s)


substTerm :: Subst -> Term -> Term
substTerm subst m = case m of
  Var x -> substVar subst x
  Data con m -> Data con (substTerm subst m)
  Tup ms -> Tup (map (substTerm subst) ms)
  Not k -> Not (substCoTerm subst k)
  Lam x m -> Lam x' (substTerm subst' m)
    where (subst', x') = substBinder subst x
  Bind s a -> Bind (substStmt subst' s) a'
    where (subst', a') = substCoBinder subst a
  Fix x m -> Fix x' (substTerm subst' m)
    where (subst', x') = substBinder subst x

substCoTerm :: Subst -> CoTerm -> CoTerm
substCoTerm subst k = case k of
  CoVar a -> substCoVar subst a
  CoData alts -> CoData [(mb_con, substCoTerm subst k) | (mb_con, k) <- alts]
  CoTup i k -> CoTup i (substCoTerm subst k)
  CoNot m -> CoNot (substTerm subst m)
  CoLam m k -> CoLam (substTerm subst m) (substCoTerm subst k)
  CoBind x s -> CoBind x' (substStmt subst' s)
    where (subst', x') = substBinder subst x

substStmt :: Subst -> Stmt -> Stmt
substStmt subst (m `Cut` k) = substTerm subst m `Cut` substCoTerm subst k
