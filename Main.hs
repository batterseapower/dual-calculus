module Main where

import qualified CallByName
import qualified CallByNeed
import qualified CallByValue
import Syntax
import LambdaCalculus

import Control.Arrow ( first, second, (&&&), (***) )

import Data.Unique.Id
import Data.Maybe
import Debug.Trace

import System.IO.Unsafe

import Text.PrettyPrint.HughesPJClass


normalise :: (Stmt -> Maybe Stmt) -> Stmt -> [Stmt]
normalise step s = s : case step s of
  Nothing -> []
  Just s  -> normalise step s


example1 = LetRec "ones" (App (App (LamVar "Cons") (LamVar "one")) (LamVar "ones"))
                  (LamVar "ones")

example2 = LetRec "map" (LamLam "f" $ LamLam "xs" $ Case (LamVar "xs") [(Just "Nil", [], LamVar "Nil_wrap"), (Just "Cons", ["y", "ys"], App (App (LamVar "Cons_wrap") (App (LamVar "f") (LamVar "x"))) $ App (App (LamVar "map") (LamVar "f")) (LamVar "ys"))])
                  (App (App (LamVar "map") (LamVar "inc")) $ App (App (LamVar "map") (LamVar "double")) (LamVar "input"))

example3_term
  = letin "f" (lam_prims "x" (Var "x"))
              (Bind (app_prims (Var "f") (Tup []) `Cut`
                    CoBind "r1" (app_prims (Var "f") (Var "2") `Cut`
                                CoBind "r2" (Tup [Var "r1", Var "r2"] `Cut`
                                             CoVar"c"))) "c") 

example3 = example3_term `Cut` CoVar "halt"

main = do
    header "Original"
    print $ pPrint example3
     -- Obtain the tuple from example3
    header "Call by name"
    mapM_ (print . pPrint) $ normalise CallByName.step example3
     -- Place demand on the first component of that tuple
    header "Call by name, first component"
    mapM_ (print . pPrint) $ normalise CallByName.step $ example3_term `Cut` CoTup 0 (CoVar "halt")
     -- Right, what does that look like in need?
    header "Call by need, first component"
    mapM_ (print . pPrint) $ normalise CallByNeed.step $ example3_term `Cut` CoTup 0 (CoVar "halt")

header s = putStrLn $ unwords [replicate 10 '=', s, replicate 10 '=']

{-
main = do
    ids1:ids2:_ <- fmap splitIdSupplyL $ initIdSupply 'm'
    print $ pPrint example1
    print $ pPrint $ dualize ids1 example1
    print $ pPrint example2
    print $ pPrint $ dualize ids2 example2
-}
