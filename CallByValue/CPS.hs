module CallByValue.CPS( cps ) where

import CallByValue.Evaluate ( lam, colam )
import Core
import Ids
import Syntax

import Data.Maybe


cps :: IdSupply -> Stmt -> Core
cps ids = runIdM ids . cpsStmt [] []


type Env   = [(Var,   Core)]
type CoEnv = [(CoVar, Core -> IdM Core)]

lookupVar   x env   = fromMaybe (CoreVar x)                      $ lookup x env
lookupCoVar a coenv = fromMaybe (return . (CoreVar a `CoreApp`)) $ lookup a coenv

cpsTerm :: Env -> CoEnv -> Term -> (Core -> IdM Core) -> IdM Core
cpsTerm env coenv m gamma = case m of
  Var x     -> gamma (lookupVar x env)
  Tup m n   -> cpsTerm env coenv m $ \x -> cpsTerm env coenv n $ \y -> gamma (CoreTup x y)
  Data m lr -> cpsTerm env coenv m $ \x -> gamma (CoreData lr x)
  Not k     -> do
    z <- fresh "notcob"
    body <- cpsCoTerm env coenv k (CoreVar z)
    gamma (CoreLam z body)
  Bind s a  -> cpsStmt env ((a, gamma) : coenv) s
  Lam x m   -> cpsTerm env coenv (lam x m) gamma

cpsCoTerm :: Env -> CoEnv -> CoTerm -> Core -> IdM Core
cpsCoTerm env coenv k z = case k of
  CoVar a    -> (lookupCoVar a coenv) z
  CoData k l -> do
    x <- fresh "altb1"
    y <- fresh "altb2"
    inlcont <- cpsCoTerm env coenv k (CoreVar x)
    inrcont <- cpsCoTerm env coenv l (CoreVar y)
    return $ CoreCase z (x, inlcont) (y, inrcont)
  CoTup fs k -> do
    x <- fresh "selb"
    cont <- cpsCoTerm env coenv k (CoreVar x)
    return $ CoreSelect z fs x cont
  CoNot m    -> do
    -- Possibly correct alternative rule:
    --cpsTerm env coenv m (return . (`CoreApp` z))
    gamma <- fresh "conotb"
    body <- cpsTerm env coenv m (return . (`CoreApp` CoreVar gamma))
    return $ z `CoreApp` CoreLam gamma body
  CoBind x s -> cpsStmt ((x, z) : env) coenv s
  CoLam m k  -> cpsCoTerm env coenv (colam m k) z

cpsStmt :: Env -> CoEnv -> Stmt -> IdM Core
cpsStmt env coenv (m `Cut` k) = cpsTerm env coenv m (cpsCoTerm env coenv k)