{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances #-}
import TestTree
import Control.Monad
import Text.Printf
import System.Random
import Test.QuickCheck hiding (numTests, Result)
import Test.QuickCheck.Gen

data BoolExpr = Var Var | T | F | And BoolExpr BoolExpr | Or BoolExpr BoolExpr | Not BoolExpr deriving (Eq, Ord, Show)
data Var = X | Y | Z deriving (Eq, Ord, Show)

repeatM = sequence . repeat

tests :: StdGen -> [(Bool, Bool, Bool)]
tests g = unGen (repeatM arbitrary) g 5

allTerms :: Int -> StdGen -> [BoolExpr]
allTerms 0 _ = [Var X, Var Y, Var Z, T, F]
allTerms (n+1) g = allTerms 0 g ++ liftM3 id [And, Or] atn atn ++ fmap Not atn
  where atn = map head (classes (results n g))

results :: Int -> StdGen -> TestResults BoolExpr
results n g = cutOff 100 (test (tests g) (allTerms n g))

instance Eval BoolExpr where
  type TestCase BoolExpr = (Bool, Bool, Bool)
  type Result BoolExpr = Bool
  eval (x, _, _) (Var X) = x
  eval (_, y, _) (Var Y) = y
  eval (_, _, z) (Var Z) = z
  eval _ T = True
  eval _ F = False
  eval e (And x y) = eval e x && eval e y
  eval e (Or x y) = eval e x || eval e y
  eval e (Not x) = not (eval e x)

main = do
  seed <- newStdGen
  let rs = results 3 seed
  printf "%d terms, %d classes, %d tests\n" (length (concat (classes rs))) (length (classes rs)) (numTests rs)
