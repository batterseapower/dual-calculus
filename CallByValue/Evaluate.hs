module CallByValue.Evaluate( step, eval, value, lam, colam, CallByValue.Evaluate.app ) where

import Substitution
import Syntax

import Data.Maybe


step :: Stmt -> Maybe Stmt
 -- If we are cutting against a non-value we can evaluate inside, do so
step (m `Cut` k) | Just (Just f, m) <- eval m = Just $ m `Cut` CoBind wildEcks (f (Var wildEcks) `Cut` k)
 -- Two possibilities remain:
 --  1) We are cutting against a value
 --  2) We are cutting against a non-value we can't go inside: i.e. a bind
 --
 -- We tackle 2) first. NB: it doesn't matter if the bind is also a value, the result is confluent
step (Bind s a `Cut` k)           = {- trace (prettyShow ("SHAREABLE", k)) $ -} Just $ substStmt (coTermSubst a k) s
 -- The only remaining possibility is 1), so we can run the other clauses
step (Data v lr `Cut` CoData k l) = Just $ v `Cut` (case lr of Inl -> k; Inr -> l)
step (Tup v w `Cut` CoTup fs k)   = Just $ (case fs of Fst -> v; Snd -> w) `Cut` k
step (Not k `Cut` CoNot m)        = Just $ m `Cut` k
step (Lam x n `Cut` CoLam m k)    = Just $ m `Cut` CoBind x (n `Cut` k)
step (v `Cut` CoBind x s)         = Just $ substStmt (termSubst x v) s
 -- We can't reduce if any one of these occurs:
 --  1) The term is a variable
 --  2) The coterm is a covariable
 --  3) The term is Fix (Fix isn't reducible in CBV. Could add CoFix to do something here though)
step _ = Nothing

-- Invariant: eval m == Just (_, n) ==> not (value n)
-- This prevents infinite loops in the normaliser: there is no point pulling out bare variables, for example
eval :: Term -> Maybe (Maybe (Term -> Term), Term)
eval (Data m lr) = do (mb_f, m) <- eval m; return (Just $ flip Data lr . fromMaybe id mb_f, m)
eval (Tup m n) | not (value m) = do (mb_f, m) <- eval m; return (Just $ \m -> Tup (fromMaybe id mb_f m) n, m)
               | not (value n) = do (mb_f, n) <- eval n; return (Just $ \n -> Tup m (fromMaybe id mb_f n), n)
eval m | value m   = Nothing
       | otherwise = Just (Nothing, m)

value :: Term -> Bool
value (Var _) = True
value (Data m _) = value m
value (Tup m n) = value m && value n
value (Not _) = True
value (Lam _ _) = True
value (Fix _ _) = False
--value (Bind (m `Cut` CoTup _ (CoVar b)) a) = value m && a == b
value (Bind _ _) = False

 -- CBV Is Dual To CBN, Reloaded: Section 3, Proposition 3
lam x m = Not (CoBind wildEcks (Var wildEcks `Cut` CoTup Fst (CoBind x (Var wildEcks `Cut` CoTup Snd (CoNot m)))))
colam m k = CoNot (Tup m (Not k))
app m n = Bind (m `Cut` (n `colam` CoVar wildAlpha)) wildAlpha
