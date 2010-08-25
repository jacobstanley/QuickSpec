{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, TypeOperators, GADTs #-}
module Main where

import Data.MemoTrie
import TestTree
import Control.Monad
import Data.Ord
import Text.Printf
import System.Random
import Test.QuickCheck hiding (numTests, Result)
import Test.QuickCheck.Gen
import Utils
import Family
import UntypedTerm
import Subst

repeatM = sequence . repeat

data IntTerm where
  X, Y, Z :: WithBound Int IntTerm -> IntTerm
  Const :: Int -> IntTerm
  Negate :: IntTerm -> IntTerm
  Plus, Times :: IntTerm -> IntTerm -> IntTerm
  deriving Eq

instance Ord IntTerm where
  compare = comparing term

type Val = (Int, Int, Int)

tests :: StdGen -> [Val]
tests g = unGen (repeatM arbitrary) g 5

type Fun = (->)

trees :: [Val] -> Int -> Int -> TestResults IntTerm
trees tcs numTests = f
  where f = memo (cutOff numTests . f')
        base = memo $ \n -> test tcs $ [ Const 0, Const 1 ] ++
                                       [ x (WithBound n (reps (f n))) | x <- [X, Y, Z] ]
        f' 0 = base 0
        f' (n+1) = base (n+1) `union` test tcs (liftM3 id [Plus, Times] ts ts ++ map Negate ts)
          where ts = reps (f n)

instance Eval IntTerm where
  type TestCase IntTerm = Val
  type Result IntTerm = Int
  eval (x,_,_) (X _) = x
  eval (_,y,_) (Y _) = y
  eval (_,_,z) (Z _) = z
  eval v (Plus t u) = eval v t + eval v u
  eval v (Times t u) = eval v t * eval v u
  eval v (Negate t) = negate (eval v t)
  eval _ (Const n) = n

instance TermLike IntTerm where
  type Bound IntTerm = Int
  term (X b) = sym $ Var "x" b
  term (Y b) = sym $ Var "y" b
  term (Z b) = sym $ Var "z" b
  term (Plus t u) = App (ConstS "+") [term t, term u]
  term (Times t u) = App (ConstS "*") [term t, term u]
  term (Negate t) = App (ConstS "-") [term t]
  term (Const n) = sym $ ConstS $ show n

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
  laws rs
