module CallByNeed.Evaluate( step ) where

import CallByName.Evaluate  ( coeval )
import Substitution
import Syntax

import Data.Maybe

-- See: http://www.mail-archive.com/haskell@haskell.org/msg14044.html


step :: Stmt -> Maybe Stmt
step s = case step' s of Just (Right s) -> Just s; _ -> Nothing


step' :: Stmt -> Maybe (Either Var Stmt)
 -- If we are cutting against an non-ANFised thing that we can pull stuff out of, do so
 -- This is safe by the inverse of the left-beta rule that allows substitution of terms for variables in statements.
step' (m `Cut` k) | Just (Just f, m) <- anfeval m = Just $ Right $ m `Cut` CoBind wildEcks (f (Var wildEcks) `Cut` k)
 -- If we are cutting against a non-covalue we can evaluate inside, do so
 -- NB: make sure that we float out the term when doing this, because this is our last
 -- chance to see that m doesn't actually depend on alpha and so we can get more sharing.
 --
 -- For example, consider the operation of the naive semantics on:
 --
 --   ((1, 2) ● fst[K]).a ● fst[x.(S)]
 --
 -- We will try and get the x.(S) to the top level so we have a covalue on the right. But if we do
 -- so naively the (S').a binding will be inside a cobind. Now, if the cobind is substituted into
 -- S because we can't reduce it further on its own, the (1, 2) ● fst[K] will be duplicated!
 --
 -- However, if we float the bind out first, we'll skip past it on subsequent steps and just evaluate
 -- (and float) within the scope of that binding. Now multiple use sites can share work done to reduce
 -- the redex.
step' (m `Cut` k) | Just (Just f, k) <- coeval k = Just $ Right $ m `Cut` CoBind wildEcks (Bind (Var wildEcks `Cut` f (CoVar wildAlpha)) wildAlpha `Cut` k)
 -- Two possibilities remain:
 --  1) We are cutting against a covalue
 --  2) We are cutting against a non-covalue we can't go inside: i.e. a cobind
 --
 -- We tackle 2) first. NB: it doesn't matter if the cobind is also a covalue, the result is confluent
step' (m `Cut` k@(CoBind x s)) = case step' s of
  Nothing -> Nothing
  Just (Right s) -> Just $ Right $ m `Cut` CoBind x s
  Just (Left y)
     -- Some other sucker is being demanded, so leave this binding alone for now
    | y /= x       -> Just (Left y)
     -- The term is already an ANF value:
    | anfvalue m   -> Just $ Right $ substStmt (termSubst x m) s
     -- The term is not an ANF value, and we can't pull stuff out (i.e. m is Fix or Bind):
    | Bind s' a <- m -> Just $ case step' s' of Nothing         -> Right $ substStmt (termSubst x m) s -- Weirdest rule: so probably terms that are blocked on a covariable should be values
                                                Just (Left y)   -> Left y
                                                Just (Right s') -> Right $ Bind s' a `Cut` k
    | Fix _ _ <- m  -> error "Not implemented: Fix"
 -- The only remaining possibility is 1), so we can run the other clauses
step' (Data con m `Cut` CoData alts) = Just $ Right $ m `Cut` head [p | (mb_con, p) <- alts, mb_con == Just con || isNothing mb_con]
step' (Tup ms `Cut` CoTup i p)       = Just $ Right $ (ms !! i) `Cut` p
step' (Not k `Cut` CoNot m)          = Just $ Right $ m `Cut` k
step' (Lam x n `Cut` CoLam m k)      = Just $ Right $ m `Cut` CoBind x (n `Cut` k)
step' (Fix _ _ `Cut` _)              = error "Not implemented: Fix" -- Just $ Right $ Fix x m `Cut` CoBind x (m `Cut` p)
step' (Bind s a `Cut` p)             = Just $ Right $ substStmt (coTermSubst a p) s
 -- We can't reduce if any one of these occurs:
 --  1) The term is a variable
step' (Var x `Cut` _) = Just $ Left x
 --  2) The coterm is a covariable
step' _               = Nothing

anfeval :: Term -> Maybe (Maybe (Term -> Term), Term)
anfeval (Data con m) | var m = return (Just (Data con), m)
anfeval (Tup ms) | (vs, m:ms) <- span var ms = return (Just $ \m -> Tup (vs ++ m : ms), m)
anfeval m | anfvalue m = Nothing
          | otherwise  = Just (Nothing, m)

anfvalue :: Term -> Bool
anfvalue (Var _) = True
anfvalue (Data _ m) = var m
anfvalue (Tup ms) = all var ms
anfvalue (Not _) = True
anfvalue (Lam _ _) = True
anfvalue (Fix _ _) = False
--anfvalue (Bind (m `Cut` CoTup _ (CoVar b)) a) = var m && a == b
anfvalue (Bind _ _) = False

var :: Term -> Bool
var (Var _) = True
var _       = False