module CallByName.Evaluate( step, coeval, covalue, lam, colam, CallByName.Evaluate.app ) where

import Substitution
import Syntax

import Data.Maybe


step :: Stmt -> Maybe Stmt
 -- If we are cutting against a non-covalue we can evaluate inside, do so
step (m `Cut` k) | Just (Just f, k) <- coeval k = Just $ Bind (m `Cut` f (CoVar wildAlpha)) wildAlpha `Cut` k
 -- Two possibilities remain:
 --  1) We are cutting against a covalue
 --  2) We are cutting against a non-covalue we can't go inside: i.e. a cobind
 --
 -- We tackle 2) first. NB: it doesn't matter if the cobind is also a covalue, the result is confluent
step (m `Cut` CoBind x s)         = {- trace (prettyShow ("SHAREABLE", m)) $ -} Just $ substStmt (termSubst x m) s
 -- The only remaining possibility is 1), so we can run the other clauses
step (Data m lr `Cut` CoData k l) = Just $ m `Cut` (case lr of Inl -> k; Inr -> l)
step (Tup m n `Cut` CoTup fs p)   = Just $ (case fs of Fst -> m; Snd -> n) `Cut` p
step (Not k `Cut` CoNot m)        = Just $ m `Cut` k
step (Lam x n `Cut` CoLam m k)    = Just $ m `Cut` CoBind x (n `Cut` k)
step (Fix x m `Cut` p)            = Just $ Fix x m `Cut` CoBind x (m `Cut` p)
step (Bind s a `Cut` p)           = Just $ substStmt (coTermSubst a p) s
 -- We can't reduce if any one of these occurs:
 --  1) The term is a variable
 --  2) The coterm is a covariable
step _ = Nothing

-- Invariants:
--  coeval k == Just (_, l)       ==> not (covalue l)
--  coeval k == Just (Nothing, l) ==> k == l
--  coeval k == Just (Just f, l)  ==> k /= l && k == f l
coeval :: CoTerm -> Maybe (Maybe (CoTerm -> CoTerm), CoTerm)
coeval (CoData k l)
  | not (covalue l) = do (mb_f, l) <- coeval l; return (Just $ \l -> CoData k (fromMaybe id mb_f l), l)
  | not (covalue k) = do (mb_f, k) <- coeval k; return (Just $ \k -> CoData (fromMaybe id mb_f k) l, k)
coeval (CoTup fs k) = do (mb_f, k) <- coeval k; return (Just $ CoTup fs . fromMaybe id mb_f, k)
coeval (CoLam m k) = do (mb_f, k) <- coeval k; return (Just $ CoLam m . fromMaybe id mb_f, k)
coeval k | covalue k = Nothing
         | otherwise = Just (Nothing, k)

covalue :: CoTerm -> Bool
covalue (CoVar _) = True
covalue (CoData k l) = covalue k && covalue l
covalue (CoTup _ k) = covalue k
covalue (CoNot _) = True
covalue (CoLam _ k) = covalue k
--covalue (CoBind x (Data _ (Var y) `Cut` k)) = covalue k && x == y
covalue (CoBind _ _) = False

 -- CBV Is Dual To CBN, Reloaded: Section 3, Proposition 4
lam x m = Bind (Data (Not (CoBind x (Data m Inr `Cut` CoVar wildAlpha))) Inl `Cut` CoVar wildAlpha) wildAlpha
colam m k = CoData (CoNot m) k
app m n = Bind (m `Cut` (n `colam` CoVar wildAlpha)) wildAlpha
