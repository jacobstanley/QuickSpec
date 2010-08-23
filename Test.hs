{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, TypeOperators #-}
module Main where

import Data.MemoTrie
import TestTree
import Control.Monad
import Text.Printf
import System.Random
import Test.QuickCheck hiding (numTests, Result)
import Test.QuickCheck.Gen
import Utils
import Family
import Term

repeatM = sequence . repeat

type Val = (Int, Int, Int)

tests :: StdGen -> [Val]
tests g = unGen (repeatM arbitrary) g 5

trees :: [Val] -> Int -> Int -> TestResults (Term Val Int)
trees tcs numTests = f
  where f = memo (cutOff numTests . f')
        base :: Int -> TestTree (Term Val Int)
        base = memo $ \n -> test tcs $ [ sym "0" $ const 0, sym "1" $ const 1,
                                         sym "x" (\(x, _, _) -> x),
                                         sym "y" (\(_, y, _) -> y),
                                         sym "z" (\(_, _, z) -> z) ]
        f' :: Int -> TestTree (Term Val Int)
        f' 0 = base 0
        f' (n+1) = base (n+1) `union` test tcs (liftM3 app3 [sym "+" $ const (+), sym "*" $ const (*)] ts ts ++ map (app (sym "-" $ const negate)) ts)
          where ts = reps (f n)
                app3 f x y = app (app f x) y

{-
constraints :: IntExpr -> [(Var, WithBound BoolAndInt IntExpr)]
constraints (Var v x) = [(v, x)]
constraints (Const _) = []
constraints (Plus t u) = constraints2 t u
constraints (Times t u) = constraints2 t u
constraints (Neg t) = constraints t

constraints2 t u = merge f fst (constraints t) (constraints u)
  where f (v, x) (_, y) = (v, x `min` y)

instances :: IntExpr -> [IntExpr]
instances = undefined
-}

main = do
  seed <- newStdGen
  let f = trees (tests seed) 100
      rs = f 2
  printf "w/ depth optimisation: %d terms, %d classes\n" (length (concat (classes rs))) (length (classes rs))
