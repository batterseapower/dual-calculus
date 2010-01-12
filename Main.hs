module Main where

import qualified CallByName.Evaluate as CallByName
-- FIXME: until I can work out how to do it properly:
-- import qualified CallByNeed.Evaluate as CallByNeed
import qualified CallByValue.Evaluate as CallByValue
import Core
import Syntax

import Control.Monad

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
lamExample1 = CoreLetRec "ones" (CoreApp (CoreApp (CoreVar "Cons") (CoreVar "one")) (CoreVar "ones")) $
              CoreVar "ones"

-- let map = \f. \xs. case xs of Nil -> Nil_wrap; Cons y ys -> Cons_wrap (f y) (map f ys)
-- in map inc (map double input)
--
-- Advanced example for supercompilation experiments
lamExample2 = CoreLetRec "map" (CoreLam "f" $ CoreLam "xs" $ CoreCase (CoreVar "xs") ("_", CoreVar "Nil_wrap") ("cons", CoreSelect (CoreVar "cons") Fst "y" $ CoreSelect (CoreVar "cons") Snd "ys" $ CoreApp (CoreApp (CoreVar "Cons_wrap") (CoreApp (CoreVar "f") (CoreVar "y"))) $ CoreApp (CoreApp (CoreVar "map") (CoreVar "f")) (CoreVar "ys"))) $
              CoreApp (CoreApp (CoreVar "map") (CoreVar "inc")) $ CoreApp (CoreApp (CoreVar "map") (CoreVar "double")) (CoreVar "input")


-- let f = \x. x
-- in (f (), f 2)
--
-- Useful for getting a feel of how lambdas work in their primitive form
dualExample1Term
  = letin "f" (CallByName.lam "x" (Var "x"))
              (Bind (CallByName.app (Var "f") (Var "()") `Cut`
                    CoBind "r1" (CallByName.app (Var "f") (Var "2") `Cut`
                                CoBind "r2" (Tup (Var "r1") (Var "r2") `Cut`
                                             CoVar "c"))) "c") 

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
dualExample3 = Bind (Not (CoBind "res1" (Not (CoBind "res2" (Tup (Var "res1") (Var "res2") `Cut` CoVar "halt")) `Cut` CoVar "a")) `Cut` CoVar "a") "a"
                 `Cut` CoBind "x" (Tup (Var "()") (Var "3") `Cut` CoTup Snd (CoBind "res" (Var "x" `Cut` CoNot (Var "res"))))

-- let fix = \x -> x x in fix fix
--
-- Obviously not well-typed in the standard rules!
dualExample4 = letin "fix" (CallByName.lam "x" $ Var "x" `CallByName.app` Var "x")
                     (Var "fix" `CallByName.app` Var "fix") `Cut` CoVar "halt"

-- let ones = 1 : ones in case ones of x:_ -> x
--
-- Useful for testing the behaviour of fixed points.
dualExample5 = letrecin "ones" (Data (Tup (Var "1") (Var "ones")) Inr)
                        (Bind (Var "ones" `Cut` CoData (CoVar "a") (CoTup Fst (CoVar "a"))) "a") `Cut` CoVar "halt"

-- letrec f = select f 1 !! fst x -> x
-- in f 2
--
-- Useful for testing the behaviour of black holes.
dualExample6 = letrecin "f" (Bind (app (Var "f") (Var "1") `Cut` CoTup Fst (CoVar "a")) "a")
                        (app (Var "f") (Var "2")) `Cut` CoVar "halt"

{-
-- See http://www.mail-archive.com/haskell@haskell.org/msg14044.html, and in particular http://www.mail-archive.com/haskell@haskell.org/msg14047.html
-- (define (make-cell)           ; Alan Bawden, 1989
-- (call-with-current-continuation
--   (lambda (return-from-make-cell)
--     (letrec ((state
--                (call-with-current-continuation
--                  (lambda (return-new-state)
--                    (return-from-make-cell
--                      (lambda (op)
--                        (case op
--                          ((set)
--                           (lambda (value)
--                             (call-with-current-continuation
--                               (lambda (return-from-access)
--                                 (return-new-state
--                                   (list value return-from-access))))))
--                          ((get) (car state)))))))))
--       ((cadr state) 'done)))))
dualExample7
  = letin "fst" (Lam "pair" (Bind (Var "pair" `Cut` CoTup 0 (CoVar "a")) "a")) $
    letin "snd" (Lam "pair" (Bind (Var "pair" `Cut` CoTup 1 (CoVar "b")) "b")) $
    letin "makecell" (callcc (Lam "return-from-make-call"
                                (letrecin "state" (callcc (Lam "return-new-state"
                                                              (Var "return-from-make-call" `app` Tup [Lam "value"
                                                                                                        (callcc (Lam "return-from-access"
                                                                                                                    (Var "return-new-state" `app` Tup [Var "value", Var "return-from-access"]))),
                                                                                                      Var "fst" `app` Var "state"]))) $
                                ((Var "snd" `app` Var "state") {- `app` Tup [] -})))) $
    letin "c" (Var "makecell") $
    Bind (Var "c" `Cut` CoTup 0 (CoBind "setter" (Var "setter" `Cut` (CoLam (Data "Foo" (Tup [])) (CoBind "_" (Var "c" `Cut` CoTup 1 (CoVar "a"))))))) "a"
  
  
  -- Tup [Bind (Var "meh" `Cut` CoVar "halt2") "_", Var "foo"] `Cut` CoBind "x" (Var "x" `Cut` CoTup 1 (CoVar "halt1"))
  -- Tup [Bind (Var "meh" `Cut` CoVar "halt2") "_", Var "foo"] `Cut` CoBind "x" (Var "x" `Cut` CoTup 1 (CoBind "y" (Var "y" `Cut` CoTup 1 (CoVar "halt1"))))
  -- Tup [Tup[Var "a", Var "b"], Var "c"] `Cut` CoTup 0 (CoBind "a" (Var "a" `Cut` CoTup 0 (CoBind "x" (Var "a" `Cut` CoTup 1 (CoBind "y" (Var "done" `Cut` CoVar "halt"))))))

-- dualExample8 = callcc (Lam "return" (Bind (Tup [Var "1", Var "2"] `Cut` CoBind "t" ((Var "return" `app` Tup [Var "1", Var "2"]) `Cut` CoTup 0 (CoBind "t2" (Var "t" `Cut` CoVar "a"))) "a")))

callcc :: Term -> Term
callcc m = Bind ((m `app` (Lam "v" $ Bind (Var "v" `Cut` CoVar "a-captured") "_")) `Cut` CoVar "a-captured") "a-captured"
-}

dualExample1Main = do
     -- Just show what we're going to work on
    header "Original"
    print $ pPrint dualExample1
     -- Obtain the tuple from example1
    header "Call by name"
    printNormalise CallByName.step dualExample1
     -- Place demand on the first component of that tuple
    header "Call by name, first component"
    printNormalise CallByName.step $ dualExample1Term `Cut` CoTup Fst (CoVar "halt")
     -- Right, what does that look like in need?
    --header "Call by need, first component"
    --printNormalise CallByNeed.step $ dualExample1Term `Cut` CoTup 0 (CoVar "halt")

exampleMain example = do
    header "Original"
    print $ pPrint example
    header "Call by name"
    printNormalise CallByName.step example
    --header "Call by need"
    --printNormalise CallByNeed.step example
    header "Call by value"
    printNormalise CallByValue.step example

printNormalise step s = do
    mapM_ (print . pPrint) steps
    when (length steps >= lIMIT) $ putStrLn $ "Terminated: number of steps exceeds " ++ show lIMIT
  where steps = take lIMIT $ normalise step s
        lIMIT = 1000

main = forM_ [(False, "Primitive lambdas", dualExample1Main),
              (True, "Call-by-name vs Call-by-need", exampleMain dualExample2),
              (False, "Call-by-value vs Call-by-coneed", exampleMain dualExample3),
              (False, "Russel non-termination", exampleMain dualExample4),
              (True,  "Fixed points", exampleMain dualExample5),
              (False, "Black holes", exampleMain dualExample6)
             ] $ \(enabled, title, example) -> when enabled $ do
        header title
        example
        putStrLn ""

header s = putStrLn $ unwords [replicate 10 '=', s, replicate 10 '=']

{-
main = do
    ids1:ids2:_ <- fmap splitIdSupplyL $ initIdSupply 'm'
    print $ pPrint example1
    print $ pPrint $ dualize ids1 example1
    print $ pPrint example2
    print $ pPrint $ dualize ids2 example2
-}
