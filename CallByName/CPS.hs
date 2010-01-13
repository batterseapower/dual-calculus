module CallByName.CPS( cps ) where

import CallByName.Evaluate ( lam, colam )
import Core
import Ids
import Syntax

import Data.Maybe


cps :: IdSupply -> Stmt -> Core
cps ids = runIdM ids . cpsStmt [] []


type Env   = [(Var,   Core -> IdM Core)]
type CoEnv = [(CoVar, Core)]

lookupVar   x env   = fromMaybe (return . (CoreVar x `CoreApp`))   $ lookup x env
lookupCoVar a coenv = fromMaybe (CoreVar a) $ lookup a coenv

cpsTerm :: Env -> CoEnv -> Term -> Core -> IdM Core
cpsTerm env coenv m gamma = case m of
  Var x     -> (lookupVar x env) gamma
  Tup m n   -> do
    x <- fresh "tupcob1"
    y <- fresh "tupcob2"
    left  <- cpsTerm env coenv m (CoreVar x)
    right <- cpsTerm env coenv n (CoreVar y)
    return $ CoreCase gamma (x, left) (y, right)
  Data m lr -> do
    x <- fresh "datacob"
    body <- cpsTerm env coenv m (CoreVar x)
    return $ CoreSelect gamma (case lr of Inl -> Fst; Inr -> Snd) x body
  Not k     -> do
    -- Possibly correct alternative rule:
    --cpsCoTerm env coenv k (return . (gamma `CoreApp`))
    z <- fresh "notb"
    body <- cpsCoTerm env coenv k (return . (CoreVar z `CoreApp`))
    return $ CoreLam z body `CoreApp` gamma
  Bind s a  -> cpsStmt env ((a, gamma):coenv) s
  Lam x m   -> cpsTerm env coenv (lam x m) gamma

cpsCoTerm :: Env -> CoEnv -> CoTerm -> (Core -> IdM Core) -> IdM Core
cpsCoTerm env coenv k z = case k of
  CoVar a    -> z (lookupCoVar a coenv)
  CoData k l -> cpsCoTerm env coenv k $ \alpha -> cpsCoTerm env coenv l $ \beta -> z (CoreTup alpha beta)
  CoTup fs k -> cpsCoTerm env coenv k $ \alpha -> z (CoreData (case fs of Fst -> Inl; Snd -> Inr) alpha)
  CoNot m    -> do
    gamma <- fresh "notcob"
    body <- cpsTerm env coenv m (CoreVar gamma)
    z (CoreLam gamma body)
  CoBind x s -> cpsStmt ((x, z):env) coenv s
  CoLam m k  -> cpsCoTerm env coenv (colam m k) z

cpsStmt :: Env -> CoEnv -> Stmt -> IdM Core
cpsStmt env coenv (m `Cut` k) = cpsCoTerm env coenv k (cpsTerm env coenv m)

{-
example1 = lam "x" (Var "x") `Cut` colam (Var "y") (CoVar "halt")
example2 = Data "Left" (Tup []) `Cut` CoData [(Just "Left", CoVar "halt"), (Just "Right", CoTup 1 (CoVar "halt"))]
example3 = Tup [Tup [], Tup [Tup [], Tup []]] `Cut` CoTup 1 (CoTup 0 (CoVar "halt"))
example4 = lam "x" (Var "x") `Cut` CoBind "id" (Bind (Var "id" `Cut` colam (Var "id") (CoVar "alpha")) "alpha" `Cut`
                                                CoBind "expensive" (Var "expensive" `Cut` colam (Var "expensive") (CoVar "halt")))


example = example4

main = do
    print example
    print $ cpsStmt [("y", Zed (CoreApp (CoreVar "y"))), ("halt", Gamma (CoreVar "halt"))] example
-}