module CallByNeed( step ) where

import CallByName   ( coeval )
import CallByValue  ( value )
import Substitution
import Syntax
import Utilities

import Control.Arrow ( first, (***) )

import Data.Maybe
import Data.List


step :: Stmt -> Maybe Stmt
step s = case cbneedInner emptyInScopeSet s of Just (Right s) -> Just s; _ -> Nothing


cbneedInner :: InScopeSet -> Stmt -> Maybe (Either Var Stmt)
 -- If we are cutting against a non-covalue we can evaluate inside, do so
cbneedInner _ (m `Cut` k) | Just (Just f, k) <- coeval k = return $ Right $ Bind (m `Cut` f (CoVar wildAlpha)) wildAlpha `Cut` k
 -- Two possibilities remain:
 --  1) We are cutting against a covalue
 --  2) We are cutting against a non-covalue we can't go inside: i.e. a cobind
 --
 -- We tackle 2) first. NB: it doesn't matter if the cobind is also a covalue, the result is confluent
cbneedInner iss (m `Cut` k@(CoBind x sk))
  | value m   = return $ Right $ substStmt (extendSubstTerm (emptySubst iss) x m) sk
  | otherwise = do
    resk <- cbneedInner (extendInScopeSetVar iss x) sk
    case resk of
       -- If we could evaluate under the cobind, do so
      Right sk -> return $ Right $ m `Cut` CoBind x sk
       -- If evaluation under the bind is blocked on a variable, we have to look elsewhere
      Left y
         -- If evaluation is blocked on a variable other than the one we bind, just bubble that up
        | y /= x
        -> return $ Left y
         -- Perhaps we can get away with just inlining part of the definition of x into the body -- just the bit that is already a value
         -- NB: important that we don't do this if the "value" is simply a variable, because then we don't make any progress!
        | (Right m, floats) <- valueize (inScopeSetInfiniteTree "float" iss) m
        , let iss' = foldl' extendInScopeSetVar iss (map fst floats)
        -> return $ Right $ floats `bindMany` substStmt (extendSubstTerm (emptySubst iss') x m) sk
         -- Only remaining possibility is that m is a non-value we can't go inside, i.e. a bind
         -- In this case we evaluate under the bind, hoping to reduce m to a value.
         --
         -- This seems to work in practice. What we need to show to prove that this works in general is
         -- that if we can't make progress by evaluating the non-value under its binding, we couldn't
         -- make progress if we actually went ahead and did the substitution.
         --
         -- The reason that this is important is that otherwise the call by need strategy would get stuck
         -- more often than the call by name one.
        | Bind sm a <- m
        -> do resm <- cbneedInner (extendInScopeSetCoVar iss a) sm
              case resm of Left y   -> return $ Left y
                           Right sm -> return $ Right $ Bind sm a `Cut` k
 -- The only remaining possibility is 1), so we can run the other clauses
cbneedInner _   (Data con m `Cut` CoData alts) = return $ Right $ m `Cut` head [p | (mb_con, p) <- alts, mb_con == Just con || isNothing mb_con]
cbneedInner _   (Tup ms `Cut` CoTup i p)       = return $ Right $ (ms !! i) `Cut` p
cbneedInner _   (Not k `Cut` CoNot m)          = return $ Right $ m `Cut` k
cbneedInner _   (Lam x n `Cut` CoLam m k)      = return $ Right $ m `Cut` CoBind x (n `Cut` k)
cbneedInner _   (Fix x m `Cut` p)              = return $ Right $ Fix x m `Cut` CoBind x (m `Cut` p)
cbneedInner iss (Bind s a `Cut` p)             = return $ Right $ substStmt (extendSubstCoTerm (emptySubst iss) a p) s
 -- We can't reduce if any one of these occurs:
 --  1) The coterm is a non-halting covariable
 --     NB: test for the OS supplied "halt" so we can inject some demand into the system!
cbneedInner _ (_ `Cut` CoVar y) | y /= "halt" = Nothing
 --  2) The term is a variable
cbneedInner _ (Var x `Cut` _)   = return $ Left x
 --  3) The term is a halting covariable
 --     NB: if we reach here have some sort of non-variable term to give to the system and we may halt
cbneedInner _ (_ `Cut` CoVar "halt") = Nothing

inScopeSetInfiniteTree :: String -> InScopeSet -> InfiniteTree String
inScopeSetInfiniteTree base iss = filterInfiniteTree (\x -> not (coVarInInScopeSet iss x) && not (varInInScopeSet iss x)) (go 0)
  where go n = Node (base ++ show n) (go $ n * 2) (go $ (n * 2) + 1)


-- Invariant: valueize ids m == (Right m, floats) ==> value m && all (not . value . snd) floats
valueize :: InfiniteTree String -> Term -> (Either Var Term, [(Var, Term)])
valueize ids (Data con m) = first (Right . Data con . injectValueize) $ valueize ids m
valueize ids (Tup ms) = (Right . Tup . map injectValueize) *** concat $ unzip $ zipWith valueize (splitInfiniteTree ids) ms
valueize ids m | value m   = (Right m, [])
               | otherwise = let x = tree_node ids in (Left x, [(x, m)])

injectValueize :: Either Var Term -> Term
injectValueize = either Var id
