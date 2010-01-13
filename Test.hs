module Test where

import qualified CallByName
import qualified CallByValue
import Duality
import Substitution
import Syntax

import Control.Monad

import Data.Unique.Id

import Test.QuickCheck
import Text.Show.Functions ()


instance Arbitrary InlInr where
    arbitrary = elements [Inl, Inr]
    coarbitrary Inl = variant 0
    coarbitrary Inr = variant 1

instance Arbitrary FstSnd where
    arbitrary = elements [Fst, Snd]
    coarbitrary Fst = variant 0
    coarbitrary Snd = variant 1

instance Arbitrary Stmt where
    arbitrary = arbitraryStmt ["input"] ["halt"]
    coarbitrary = error "Stmt: coarbitrary"

arbitraryStmt :: [Var] -> [CoVar] -> Gen Stmt
arbitraryStmt vs covs = liftM2 Cut (arbitraryTerm vs covs) (arbitraryCoTerm vs covs)

arbitraryTerm :: [Var] -> [CoVar] -> Gen Term
arbitraryTerm vs covs = sized $ \n ->
  if n <= 0
   then liftM Var (elements vs)
   else oneof [
      resize (n - 1)     $ liftM2 Data (arbitraryTerm vs covs) arbitrary,
      resize (n `div` 2) $ liftM2 Tup (arbitraryTerm vs covs) (arbitraryTerm vs covs),
      resize (n - 1)     $ liftM Not (arbitraryCoTerm vs covs),
      resize (n - 1)     $ let a = "a" ++ show (length covs) in liftM (flip Bind a) (arbitraryStmt vs (a : covs))
    ]

arbitraryCoTerm :: [Var] -> [CoVar] -> Gen CoTerm
arbitraryCoTerm vs covs = sized $ \n ->
  if n <= 0
   then liftM CoVar (elements covs)
   else oneof [
      resize (n `div` 2) $ liftM2 CoData (arbitraryCoTerm vs covs) (arbitraryCoTerm vs covs),
      resize (n - 1)     $ liftM2 CoTup arbitrary (arbitraryCoTerm vs covs),
      resize (n - 1)     $ liftM CoNot (arbitraryTerm vs covs),
      resize (n - 1)     $ let x = "x" ++ show (length vs) in liftM (CoBind x) (arbitraryStmt (x : vs) covs)
    ]


main :: IdSupply -> IO ()
main ids = do
    -- CBV Is Dual To CBN: Proposition 3.1 -- Duality is an involution
  quickCheck $ \s -> dualizeStmt (dualizeStmt s) == s
    -- CBV Is Dual To CBN: Proposition 5.1 -- Call-by-value is dual to call-by-name
  quickCheck $ \s -> CallByName.step s == fmap dualizeStmt (CallByValue.step (dualizeStmt s))
    -- CBV Is Dual To CBN: Proposition 5.2 -- Under call-by-value, implication can be defined by ...
  quickCheck $ forAllTwoHoleCtxt $ \ctxt -> forAll (arbitraryTerm ["x"] []) $ \m ->
                 CallByValue.step (ctxt (CallByValue.lam "x" m) (CallByValue.colam (Var "y") (CoVar "halt"))) == CallByValue.step (ctxt (Lam "x" m) (CoLam (Var "y") (CoVar "halt")))
    -- CBV Is Dual To CBN: Proposition 5.3 -- Under call-by-name, implication can be defined by ...
  quickCheck $ forAllTwoHoleCtxt $ \ctxt -> forAll (arbitraryTerm ["x"] []) $ \m ->
                 normalise CallByName.step (ctxt (CallByName.lam "x" m) (CallByValue.colam (Var "y") (CoVar "halt"))) == normalise CallByName.step (ctxt (Lam "x" m) (CoLam (Var "y") (CoVar "halt")))
    -- CBV Is Dual To CBN: Proposition 6.3 -- The call-by-value and call-by-name CPS translations are dual
  quickCheck $ \s -> CallByValue.cps ids s == CallByName.cps ids (dualizeStmt s)

normalise :: (a -> Maybe a) -> a -> Maybe a
normalise step what = go 50 what
  where go 0 _ = Nothing
        go n what = case step what of Just what -> go (n - 1) what
                                      Nothing   -> Just what

forAllTwoHoleCtxt :: Testable b => ((Term -> CoTerm -> Stmt) -> b) -> Property
forAllTwoHoleCtxt test = forAll (arbitraryStmt ["f"] ["a"]) $ \stmt -> test $ \f a -> substStmt (extendSubstTerm (coTermSubst "a" a) "f" f) stmt