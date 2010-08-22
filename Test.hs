{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, TypeOperators #-}
module Main where

import Data.MemoTrie
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
  where atn = reps (results n g)

trees :: Int -> StdGen -> (Int :->: TestTree IntExpr)
-- Hmm, we can even easily make the sound depth optimisation this
-- way---just make the code for n+1 tests base itself on the code for
-- n tests. All we really need is union for that. Plus an operation to
-- find out what new representatives appear at depth n of the testing
-- tree.
trees numTests gen = t
  where t = trie f
        f 0 = test allTests [Var X, Var Y, Var Z, Const 0, Const 1]
        f (n+1) = untrie t 0 `union` test allTests (liftM3 id [Plus, Times] ts ts ++ map Neg ts)
          where ts = reps (cutOff numTests (untrie t n))
        allTests = tests gen

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
      f = untrie (trees 100 seed)
      rs' = cutOff 100 (f 2)
  printf "%d terms, %d classes, %d tests\n" (length (concat (classes rs))) (length (classes rs)) (numTests rs)
  printf "w/ depth optimisation: %d terms, %d classes\n" (length (concat (classes rs'))) (length (classes rs'))
