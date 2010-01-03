module CallByNeed( step ) where

import CallByName   ( coeval )
import CallByValue  ( value )
import Substitution
import Syntax
import Utilities

import Control.Arrow ( first, (***) )
import Control.Applicative
import Control.Monad

import Data.Maybe

import Debug.Trace


step :: Stmt -> Maybe Stmt
step s = case stepStmt emptyInScopeSet s of Step s -> Just s; Halt -> trace "Halt" Nothing; Neutral x -> trace x Nothing -- _ -> Nothing


data StepM a = Halt
             | Neutral Var
             | Step a

instance Functor StepM where
    fmap = liftM

instance Applicative StepM where
    pure = return
    (<*>) = ap

instance Monad StepM where
    return = Step
    
    Halt      >>= _   = Halt
    Neutral x >>= _   = Neutral x
    Step a    >>= fmy = fmy a

stepStmt :: InScopeSet -> Stmt -> StepM Stmt
 -- Reduce non-covalues by either:
 --  1) Pulling out sub-coterms in coevaluation contexts
stepStmt _   (m `Cut` k) | Just (Just f, k) <- coeval k = return $ Bind (m `Cut` f (CoVar wildAlpha)) wildAlpha `Cut` k
 --  2) Reducing into cobinds
stepStmt iss (m `Cut` k@(CoBind x sk)) = case stepStmt (extendInScopeSetVar iss x) sk of
  Neutral y | y == x -> fixup                      <$> stepTerm iss m
  step_s             -> (\s -> m `Cut` CoBind x s) <$> step_s
  where  -- If there are no floats then we have reduced inside m on the way to making it a value:
         -- just store the progress we have made in the syntax tree
        fixup (m, Nothing)     = m `Cut` k
         -- If there are floats then we have a piece of value to substitute it. If we just bound it
         -- then we would go into an infinite loop here, so we do a compulsory substitution
        fixup (m, Just floats) = bindMany floats $ substStmt (extendSubstTerm (emptySubst iss) x m) sk
 -- If we reach here we certainly have a covalue. However, we can't reduce if any one of these occurs:
 --  1) The term is a variable
stepStmt _   (Var x `Cut` _) = Neutral x
 --  2) The coterm is a covariable cut against a term we are not guaranteed to make further progress on.
 --     The reason we check for potential progress is to make sure that we have at least some demand...
stepStmt _   (m `Cut` CoVar x) | not (reducible m) = trace x Halt
  where reducible m = case m of Bind _ _ -> True; Fix _ _ -> True; _ -> False
 -- The only case remaining is that this is a cut of a value against a covalue that we
 -- will certainly be able to make progress on -- no variables block us
stepStmt _   (Data con m `Cut` CoData alts) = return $ m `Cut` head [p | (mb_con, p) <- alts, mb_con == Just con || isNothing mb_con]
stepStmt _   (Tup ms `Cut` CoTup i p)       = return $ (ms !! i) `Cut` p
stepStmt _   (Not k `Cut` CoNot m)          = return $ m `Cut` k
stepStmt _   (Lam x n `Cut` CoLam m k)      = return $ m `Cut` CoBind x (n `Cut` k)
stepStmt iss (Bind s a `Cut` p)             = return $ substStmt (extendSubstCoTerm (emptySubst iss) a p) s
stepStmt iss (Fix x m `Cut` p)              = (\m -> m `Cut` p) <$> stepTermFix iss x m


 -- Used when further progress in a term depends on the term becoming more value-like
stepTerm :: InScopeSet -> Term -> StepM (Term, Maybe [(Var, Term)])
stepTerm iss m | (Right m, floats) <- valueize (inScopeSetInfiniteTree "float" iss) m = return $ (m, Just floats)
stepTerm iss (Bind sm a) = (\sm -> (Bind sm a, Nothing)) <$> stepStmt (extendInScopeSetCoVar iss a) sm
stepTerm iss (Fix x m) = (\m -> (m, Nothing)) <$> stepTermFix iss x m

-- Fixpoints need special treatment: we don't want to expand them blindly because we get
-- work duplication, and we want to start the expansion only when we really have to i.e.
-- when the coterm is a covalue.
--
-- Standard semantics (note the duplicated M):
--  (fix x. M) ● P = (fix x. M) ● x.(M ● P)
stepTermFix :: InScopeSet -> Var -> Term -> StepM Term
stepTermFix iss x m = case stepTerm iss' m of
                         Neutral y | y == x -> error "Black Hole"
                         step_m             -> fixup <$> step_m
  where
    iss' = extendInScopeSetCoVar iss x
    
     -- Case 1: if we could reduce inside the Fix to make it more like a value without getting there, do that
    fixup (m, Nothing)     = Fix x m
     -- Case 2: we have some sort of value. We must bind any floats inside the fix, and make the valueised part
     -- of the original expression available to the guy cutting against the fix by duplicating it outside
    fixup (m, Just floats) = Bind (Fix z (Bind (extractors $ Tup ms `Cut` CoVar c) c)
                                    `Cut` CoBind z (extractors $ m `Cut` CoVar d)) d
      where
        Node z (Node c _ _) (Node d _ _) = inScopeSetInfiniteTree "floatfix" (foldl extendInScopeSetVar iss' $ map fst floats)
        (xs, ms) = unzip $ (x, m) : floats
         -- TODO: could avoid binding the tuple if binding < 2 things
        extractors s = foldr (\(i, x) s -> Var z `Cut` CoTup i (CoBind x s)) s ([0..] `zip` xs)


inScopeSetInfiniteTree :: String -> InScopeSet -> InfiniteTree String
inScopeSetInfiniteTree base iss = filterInfiniteTree (\x -> not (coVarInInScopeSet iss x) && not (varInInScopeSet iss x)) (go 1)
  where go n = Node (base ++ show n) (go $ n * 2) (go $ (n * 2) + 1)

-- Invariant: valueize ids m == (Right m, floats) ==> value m && all (not . value . snd) floats
valueize :: InfiniteTree String -> Term -> (Either Var Term, [(Var, Term)])
valueize ids (Data con m) = first (Right . Data con . injectValueize) $ valueize ids m
valueize ids (Tup ms) = (Right . Tup . map injectValueize) *** concat $ unzip $ zipWith valueize (splitInfiniteTree ids) ms
valueize ids m | value m   = (Right m, [])
               | otherwise = let x = tree_node ids in (Left x, [(x, m)])

injectValueize :: Either Var Term -> Term
injectValueize = either Var id

{-
decompose :: (Stmt -> a) -> Stmt -> Maybe (Either Var (Stmt -> a, Stmt))
 -- Reduce non-covalues by either:
 --  1) Pulling out sub-coterms in coevaluation contexts
decompose f s@(_ `Cut` k) | Just (Just _, _) <- coeval k = return $ Right (f, s)
 --  2) Reducing into cobinds
decompose f (m `Cut` k@(CoBind x sk)) = case decompose (\s -> f $ m `Cut` CoBind x s) sk of
    Just (Left y) | y == x -> decomposeTerm f (\m -> m `Cut` k) m
    res                    -> res
 -- If we reach here we certainly have a covalue. Fixpoints need special treatment:
 -- we don't want to expand them blindly because we get work duplication, and we want
 -- to start the expansion only when we really have to i.e. when the coterm is a covalue
decompose f (Fix x m `Cut` p) = case decomposeTerm f (\m -> Fix x m `Cut` p) m of
    Just (Left y) | y == x -> error "Black Hole?"
    res                    -> res
 -- We can't reduce if any one of these occurs:
 --  1) The term is a variable
decompose f (Var x `Cut` _) = return $ Left x
 --  2) The coterm is a covariable
decompose f (_ `Cut` CoVar a) = Nothing
 -- The only case remaining is that this is a cut of a value against a covalue that we
 -- will certainly be able to make progress on -- no variables block us
decompose f s = return $ Right (f, s)

 -- Used when further progress in a term depends on a covalue becoming more value-like
decomposeTerm :: (Stmt -> a) -> (Term -> Stmt) -> Term -> Maybe (Either Var (Stmt -> a, Stmt))
decomposeTerm f ft m
  | valueizable m  = return $ Right (f, ft m)
  | Bind sm a <- m = decompose (\s -> f $ ft $ Bind s a) sm
  | Fix x m <- m   = case decomposeTerm f (\m -> ft $ Fix x m) m of
                         Just (Left y) | y == x -> error "Black Hole?"
                         res                    -> res

valueizable (Data _ _) = True
valueizable (Tup _) = True
valueizable m = value m
-}