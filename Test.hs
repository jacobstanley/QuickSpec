{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances #-}
module Main where

import TestTree
import Control.Monad
import Text.Printf
import System.Random
import Test.QuickCheck hiding (numTests, Result)
import Test.QuickCheck.Gen

data IntExpr = Var Var | Const Int | Plus IntExpr IntExpr | Times IntExpr IntExpr | Neg IntExpr deriving (Eq, Ord, Show)
data Var = X | Y | Z deriving (Eq, Ord, Show)

repeatM = sequence . repeat

tests :: StdGen -> [(Int, Int, Int)]
tests g = unGen (repeatM arbitrary) g 5

allTerms :: Int -> StdGen -> [IntExpr]
allTerms 0 _ = [Var X, Var Y, Var Z, Const 0, Const 1]
allTerms (n+1) g = allTerms 0 g ++ liftM3 id [Plus, Times] atn atn ++ fmap Neg atn
  where atn = map head (classes (results n g))

results :: Int -> StdGen -> TestResults IntExpr
results n g = cutOff 100 (test (tests g) (allTerms n g))

instance Eval IntExpr where
  type TestCase IntExpr = (Int, Int, Int)
  type Result IntExpr = Int
  eval (x, _, _) (Var X) = x
  eval (_, y, _) (Var Y) = y
  eval (_, _, z) (Var Z) = z
  eval _ (Const x) = x
  eval e (Plus x y) = eval e x + eval e y
  eval e (Times x y) = eval e x * eval e y
  eval e (Neg x) = negate (eval e x)

main = do
  seed <- newStdGen
  let rs = results 2 seed
  printf "%d terms, %d classes, %d tests\n" (length (concat (classes rs))) (length (classes rs)) (numTests rs)
