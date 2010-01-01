module CallByNeed( step ) where

import CallByName   ( coeval )
import CallByValue  ( value )
import Substitution
import Syntax

import Control.Arrow ( first, (***) )

import Data.Unique.Id
import Data.Maybe


step :: Stmt -> Maybe Stmt
step s = case cbneedInner s of Just (Right s) -> Just s; _ -> Nothing


cbneedInner :: Stmt -> Maybe (Either Var Stmt)
 -- If we are cutting against a non-covalue we can evaluate inside, do so
cbneedInner (m `Cut` k) | Just (Just f, k) <- coeval k = return $ Right $ Bind (m `Cut` f (CoVar alpha)) alpha `Cut` k
 -- Two possibilities remain:
 --  1) We are cutting against a covalue
 --  2) We are cutting against a non-covalue we can't go inside: i.e. a cobind
 --
 -- We tackle 2) first. NB: it doesn't matter if the cobind is also a covalue, the result is confluent
cbneedInner (m `Cut` k@(CoBind x sk))
  | value m   = return $ Right $ substTermS x m sk
  | otherwise = do
    resk <- cbneedInner sk
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
        | (Right m, floats) <- valueize wildIdSupply m
        -> return $ Right $ floats `bindMany` substTermS x m sk
         -- Only remaining possibility is that m is a non-value we can't go inside, i.e. a bind
         -- In this case we evaluate under the bind, hoping to reduce m to a value
        | Bind sm x <- m
        -> do resm <- cbneedInner sm
              case resm of Left y   -> return $ Left y
                           Right sm -> return $ Right $ Bind sm x `Cut` k
 -- The only remaining possibility is 1), so we can run the other clauses
cbneedInner (Data con m `Cut` CoData alts) = return $ Right $ m `Cut` head [p | (mb_con, p) <- alts, mb_con == Just con || isNothing mb_con]
cbneedInner (Tup ms `Cut` CoTup i p)       = return $ Right $ (ms !! i) `Cut` p
cbneedInner (Not k `Cut` CoNot m)          = return $ Right $ m `Cut` k
cbneedInner (Lam x m `Cut` CoLam n k)      = return $ Right $ m `Cut` CoBind x (n `Cut` k)
cbneedInner (Fix x m `Cut` p)              = return $ Right $ Fix x m `Cut` CoBind x (m `Cut` p)
cbneedInner (Bind s a `Cut` p)             = return $ Right $ substCoTermS a p s
 -- We can't reduce if any one of these occurs:
 --  1) The coterm is a non-halting covariable
 --     NB: test for the OS supplied "halt" so we can inject some demand into the system!
cbneedInner (_ `Cut` CoVar y) | y /= "halt" = Nothing
 --  2) The term is a variable
cbneedInner (Var x `Cut` _)   = return $ Left x
 --  3) The term is a halting covariable
 --     NB: if we reach here have some sort of non-variable term to give to the system and we may halt
cbneedInner (_ `Cut` CoVar "halt") = Nothing


-- Invariant: valueize ids m == (Right m, floats) ==> value m && all (not . value . snd) floats
valueize :: IdSupply -> Term -> (Either Var Term, [(Var, Term)])
valueize ids (Data con m) = first (Right . Data con . injectValueize) $ valueize ids m
valueize ids (Tup ms) = (Right . Tup . map injectValueize) *** concat $ unzip $ zipWith valueize (splitIdSupplyL ids) ms
valueize ids m | value m   = (Right m, [])
               | otherwise = let x = show $ idFromSupply ids in (Left x, [(x, m)])

injectValueize :: Either Var Term -> Term
injectValueize = either Var id
