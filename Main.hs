module Main where

import qualified CallByName
import qualified CallByNeed
import qualified CallByValue
import Syntax
import LambdaCalculus

import Text.PrettyPrint.HughesPJClass


normalise :: (Stmt -> Maybe Stmt) -> Stmt -> [Stmt]
normalise step s = s : case step s of
  Nothing -> []
  Just s  -> normalise step s


-- letrec ones = one : ones in ones
--
-- Simple demonstration of infinite data
lamExample1 = LetRec "ones" (App (App (LamVar "Cons") (LamVar "one")) (LamVar "ones"))
                     (LamVar "ones")

-- let map = \f. \xs. case xs of Nil -> Nil_wrap; Cons y ys -> Cons_wrap (f y) (map f ys)
-- in map inc (map double input)
--
-- Advanced example for supercompilation experiments
lamExample2 = LetRec "map" (LamLam "f" $ LamLam "xs" $ Case (LamVar "xs") [(Just "Nil", [], LamVar "Nil_wrap"), (Just "Cons", ["y", "ys"], App (App (LamVar "Cons_wrap") (App (LamVar "f") (LamVar "y"))) $ App (App (LamVar "map") (LamVar "f")) (LamVar "ys"))])
                     (App (App (LamVar "map") (LamVar "inc")) $ App (App (LamVar "map") (LamVar "double")) (LamVar "input"))


-- let f = \x. x
-- in (f (), f 2)
--
-- Useful for getting a feel of how lambdas work in their primitive form
dualExample1Term
  = letin "f" (CallByName.lam "x" (Var "x"))
              (Bind (CallByName.app (Var "f") (Tup []) `Cut`
                    CoBind "r1" (CallByName.app (Var "f") (Var "2") `Cut`
                                CoBind "r2" (Tup [Var "r1", Var "r2"] `Cut`
                                             CoVar"c"))) "c") 

dualExample1 = dualExample1Term `Cut` CoVar "halt"

-- let id = (\x. x) (\x. x)
-- in id id
--
-- Useful for showing the difference between call by name and call by need,
-- since call by need evaluates the application in "id" only once
dualExample2 = letin "id" (app (Lam "x" (Var "x")) (Lam "x" (Var "x")))
                          (app (Var "id") (Var "id")) `Cut` CoVar "halt"

dualExample1Main = do
     -- Just show what we're going to work on
    header "Original"
    print $ pPrint dualExample1
     -- Obtain the tuple from example1
    header "Call by name"
    mapM_ (print . pPrint) $ normalise CallByName.step dualExample1
     -- Place demand on the first component of that tuple
    header "Call by name, first component"
    mapM_ (print . pPrint) $ normalise CallByName.step $ dualExample1Term `Cut` CoTup 0 (CoVar "halt")
     -- Right, what does that look like in need?
    header "Call by need, first component"
    mapM_ (print . pPrint) $ normalise CallByNeed.step $ dualExample1Term `Cut` CoTup 0 (CoVar "halt")

dualExample2Main = do
    header "Original"
    print $ pPrint dualExample2
    header "Call by name"
    mapM_ (print . pPrint) $ normalise CallByName.step dualExample2
    header "Call by need"
    mapM_ (print . pPrint) $ normalise CallByNeed.step dualExample2

main = dualExample2Main

header s = putStrLn $ unwords [replicate 10 '=', s, replicate 10 '=']

{-
main = do
    ids1:ids2:_ <- fmap splitIdSupplyL $ initIdSupply 'm'
    print $ pPrint example1
    print $ pPrint $ dualize ids1 example1
    print $ pPrint example2
    print $ pPrint $ dualize ids2 example2
-}
