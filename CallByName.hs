module CallByName( step, coeval, covalue, lam, colam, CallByName.app ) where

import Substitution
import Syntax
import Utilities

import Data.Maybe


step :: Stmt -> Maybe Stmt
 -- If we are cutting against a non-covalue we can evaluate inside, do so
step (m `Cut` k) | Just (Just f, k) <- coeval k = Just $ Bind (m `Cut` f (CoVar wildAlpha)) wildAlpha `Cut` k
 -- Two possibilities remain:
 --  1) We are cutting against a covalue
 --  2) We are cutting against a non-covalue we can't go inside: i.e. a cobind
 --
 -- We tackle 2) first. NB: it doesn't matter if the cobind is also a covalue, the result is confluent
step (m `Cut` CoBind x s)           = {- trace (prettyShow ("SHAREABLE", m)) $ -} Just $ substStmt (termSubst x m) s
 -- The only remaining possibility is 1), so we can run the other clauses
step (Data con m `Cut` CoData alts) = Just $ m `Cut` head [p | (mb_con, p) <- alts, mb_con == Just con || isNothing mb_con]
step (Tup ms `Cut` CoTup i p)       = Just $ (ms !! i) `Cut` p
step (Not k `Cut` CoNot m)          = Just $ m `Cut` k
step (Lam x n `Cut` CoLam m k)      = Just $ m `Cut` CoBind x (n `Cut` k)
step (Fix x m `Cut` p)              = Just $ Fix x m `Cut` CoBind x (m `Cut` p)
step (Bind s a `Cut` p)             = Just $ substStmt (coTermSubst a p) s
 -- We can't reduce if any one of these occurs:
 --  1) The term is a variable
 --  2) The coterm is a covariable
step _ = Nothing

-- Invariant: coeval k == Just (_, l) ==> not (covalue l)
-- This prevents infinite loops in the normaliser: there is no point pulling out bare covariables, for example
coeval :: CoTerm -> Maybe (Maybe (CoTerm -> CoTerm), CoTerm)
coeval (CoData alts)
  | Just (remains, (mb_con, k)) <- uncons remains
  = do (mb_f, k) <- coeval k; return (Just $ \k -> CoData (remains ++ [(mb_con, fromMaybe id mb_f k)] ++ covalues), k)
  where (remains, covalues) = spanRev (covalue . snd) alts
coeval (CoTup i k) = do (mb_f, k) <- coeval k; return (Just $ CoTup i . fromMaybe id mb_f, k)
coeval k | covalue k = Nothing
         | otherwise = Just (Nothing, k)

covalue :: CoTerm -> Bool
covalue (CoVar _) = True
covalue (CoData alts) = all (covalue . snd) alts
covalue (CoTup _ k) = covalue k
covalue (CoNot _) = True
covalue (CoLam _ k) = covalue k
covalue (CoBind x (Data _ (Var y) `Cut` k)) = covalue k && x == y
covalue (CoBind x (Var y `Cut` k)) = covalue k && x == y -- NB: not strictly as per Wadlers definition, but saves some fiddling in the cbneed strategy
covalue (CoBind _ _) = False

 -- CBV Is Dual To CBN, Reloaded: Section 3, Proposition 4
lam x m = Bind (Data "Left" (Not (CoBind x (Data "Right" m `Cut` CoVar wildAlpha))) `Cut` CoVar wildAlpha) wildAlpha
colam m k = CoData [(Just "Left", CoNot m), (Just "Right", k)]
app m n = Bind (m `Cut` (n `colam` CoVar wildAlpha)) wildAlpha
