module CallByValue( step, eval, value ) where

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
step (Bind s a `Cut` k)             = {- trace (prettyShow ("SHAREABLE", k)) $ -} Just $ substStmt (coTermSubst a k) s
 -- The only remaining possibility is 1), so we can run the other clauses
step (Data con v `Cut` CoData alts) = Just $ v `Cut` head [k | (mb_con, k) <- alts, mb_con == Just con || isNothing mb_con]
step (Tup vs `Cut` CoTup i k)       = Just $ (vs !! i) `Cut` k
step (Not k `Cut` CoNot m)          = Just $ m `Cut` k
step (Lam x n `Cut` CoLam m k)      = Just $ m `Cut` CoBind x (n `Cut` k)
step (v `Cut` CoBind x s)           = Just $ substStmt (termSubst x v) s
 -- We can't reduce if any one of these occurs:
 --  1) The term is a variable
 --  2) The coterm is a covariable
 --  3) The term is Fix (Fix isn't reducible in CBV. Could add CoFix to do something here though)
step _ = Nothing

-- Invariant: eval m == Just (_, n) ==> not (value n)
-- This prevents infinite loops in the normaliser: there is no point pulling out bare variables, for example
eval :: Term -> Maybe (Maybe (Term -> Term), Term)
eval (Data con m) = do (mb_f, m) <- eval m; return (Just $ Data con . fromMaybe id mb_f, m)
eval (Tup ms) | (vs, m:ms) <- span value ms = do (mb_f, m) <- eval m; return (Just $ \m -> Tup (vs ++ fromMaybe id mb_f m : ms), m)
eval m | value m   = Nothing
       | otherwise = Just (Nothing, m)

value :: Term -> Bool
value (Var _) = True
value (Data _ m) = value m
value (Tup ms) = all value ms
value (Not _) = True
value (Lam _ _) = True
value (Fix _ _) = False
value (Bind (m `Cut` CoTup _ (CoVar b)) a) = value m && a == b
value (Bind (m `Cut` CoVar b) a) = value m && a == b -- NB: not strictly as per Wadler, as for covalue
value (Bind _ _) = False