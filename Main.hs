module Main where

import qualified CallByName
import qualified CallByNeed
import qualified CallByValue
import Syntax
import LambdaCalculus

import Text.PrettyPrint.HughesPJClass


-- TODO:
--  * Prove call by need correct (or otherwise)
--   # The definition for covalue and value may be incorrect: are cuts (V ● a).a really values in general, and not just at the top level?
--  * Implement the strategy dual to call by need


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
-- Useful for showing the difference between call by name and call by need
-- (or call by value), since the latter two evaluate the application in "id" only once
dualExample2 = letin "id" (app (Lam "x" (Var "x")) (Lam "x" (Var "x")))
                          (app (Var "id") (Var "id")) `Cut` CoVar "halt"

-- ([res1.([res2.((res1, res2) ● halt)]~ ● a)]~ ● a).a ● x.(((), 3) ● 1 !! res.(x ● ~(res)))
--
-- An example that shows the difference between call by value and the strategy
-- dual to call by need. Because the coterm bound to "a" is used non-linearly,
-- we have the opportunity to force it to perform the cut of Tup against CoTup
-- more than once, which leads to inefficiency.
--
-- The reason that this strategy has not recieved more attention is that in
-- lambda calculus, the coterm (continuation) is typically used linearly, so
-- there is little to be gained by memoization, even though you see CBV reductions
-- like the following that at first glance seem to introduce work duplication:
--
--  ((\x. x) ● (\x. x @ a1)).a1 ● id.((id ● (id @ a1)).a1 ● halt)
-- -->
--  (\x. x) ● (\x. x @ id.((id ● (id @ a1)).a1 ● halt))
dualExample3 = Bind (Not (CoBind "res1" (Not (CoBind "res2" (Tup [Var "res1", Var "res2"] `Cut` CoVar "halt")) `Cut` CoVar "a")) `Cut` CoVar "a") "a"
                 `Cut` CoBind "x" (Tup [Tup [], Var "3"] `Cut` CoTup 1 (CoBind "res" (Var "x" `Cut` CoNot (Var "res"))))

-- let russel = \u@(MkU p) -> p u in russel (MkU russel)
--
-- Based on the following example from the GHC users guide (http://www.haskell.org/ghc/docs/latest/html/users_guide/bugs.html):
--  data U = MkU (U -> Bool)
--
--  russel :: U -> Bool
--  russel u@(MkU p) = not $ p u
--
--  x :: Bool
--  x = russel (MkU russel)
dualExample4 = letin "russel" (Lam "u" (Bind (Var "u" `Cut` CoData [(Just "MkU", CoBind "russel'" (Var "russel'" `app` Var "u" `Cut` CoVar "wildalpha"))]) wildAlpha))
                     (Var "russel" `app` Data "MkU" (Var "russel")) `Cut` CoVar "halt"

-- let ones = 1 : ones in case ones of x:_ -> x
--
-- Useful for testing the behaviour of fixed points.
dualExample5 = letrecin "ones" (Data "Cons" $ Tup [Var "1", Var "ones"])
                        (Bind (Var "ones" `Cut` CoData [(Just "Cons", CoTup 0 (CoVar "a"))]) "a") `Cut` CoVar "halt"

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

exampleMain example = do
    header "Original"
    print $ pPrint example
    header "Call by name"
    mapM_ (print . pPrint) $ normalise CallByName.step example
    header "Call by need"
    mapM_ (print . pPrint) $ normalise CallByNeed.step example
    header "Call by value"
    mapM_ (print . pPrint) $ normalise CallByValue.step example

main = exampleMain dualExample5

header s = putStrLn $ unwords [replicate 10 '=', s, replicate 10 '=']

{-
main = do
    ids1:ids2:_ <- fmap splitIdSupplyL $ initIdSupply 'm'
    print $ pPrint example1
    print $ pPrint $ dualize ids1 example1
    print $ pPrint example2
    print $ pPrint $ dualize ids2 example2
-}
