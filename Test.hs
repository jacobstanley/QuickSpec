{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, TypeOperators #-}
module Main(main) where

import Data.MemoTrie
import TestTree
import Control.Monad
import Text.Printf
import System.Random
import Test.QuickCheck hiding (numTests, Result)
import Test.QuickCheck.Gen
import Utils
import Family

data BoolAndInt = C Bool Int deriving Eq

instance Ord BoolAndInt where
  C True x <= C True y = x <= y
  C False x <= C False y = x <= y
  C True x <= C False y = x < y
  C False x <= C True y = x <= y

instance HasTrie BoolAndInt where
  data BoolAndInt :->: a = B ((Bool, Int) :->: a)
  trie f = B (trie (\(x, y) -> f (C x y)))
  untrie (B t) = \(C x y) -> f' (x, y)
    where f' = untrie t
  enumerate (B t) = [ (C x y, z) | ((x, y), z) <- enumerate t ]

data IntExpr = Var Var (WithBound BoolAndInt IntExpr) | Const Int | Plus IntExpr IntExpr | Times IntExpr IntExpr | Neg IntExpr deriving (Eq, Ord)
data Var = X | Y | Z deriving (Eq, Ord, Show)
instance Show IntExpr where
  show (Var x _) = show x
  show (Const n) = show n
  show (Plus t u) = "(" ++ show t ++ ")+(" ++ show u ++ ")"
  show (Times t u) = "(" ++ show t ++ ")*(" ++ show u ++ ")"
  show (Neg t) = "-" ++ show t

repeatM = sequence . repeat

tests :: StdGen -> [(Int, Int, Int)]
tests g = unGen (repeatM arbitrary) g 5

trees :: Int -> StdGen -> BoolAndInt -> TestResults IntExpr
-- Hmm, we can even easily make the sound depth optimisation this
-- way---just make the code for n+1 tests base itself on the code for
-- n tests. All we really need is union for that. Plus an operation to
-- find out what new representatives appear at depth n of the testing
-- tree.
--
-- Actually---we currently kill a branch when it hasn't been refined
-- for 100 steps, in which case the depth optimisation is perfectly
-- sound! The problematic terms don't get tested any more at higher
-- depth.
trees numTests gen = f
  where f = memo (cutOff numTests . f')
        base = memo $ \n -> test allTests $ [ Const 0, Const 1 ] ++
                                            [ Var x (WithBound n (reps (f n))) | x <- [X, Y, Z] ]
        f' (C False 0) = base (C False 0)
        f' (C False (n+1)) = base (C False (n+1)) `union` test allTests (liftM3 id [Plus, Times] ts ts ++ map Neg ts)
          where ts = reps (f (C False n))
        f' (C True 0) = base (C True 0) `union` test allTests (map Neg (reps (cutOff numTests (base (C True 0)))))
        f' (C True (n+1)) = base (C True (n+1)) `union` test allTests (map Neg (reps (cutOff numTests (base (C True (n+1))))))
                                          `union` test allTests (liftM3 id [Plus, Times] ts ts)
                                          `union` test allTests (map Neg (reps (f (C False (n+1)))))
          where ts = reps (f (C True n))
        allTests = tests gen

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

instance Eval IntExpr where
  type TestCase IntExpr = (Int, Int, Int)
  type Result IntExpr = Int
  eval (x, _, _) (Var X _) = x
  eval (_, y, _) (Var Y _) = y
  eval (_, _, z) (Var Z _) = z
  eval _ (Const x) = x
  eval e (Plus x y) = eval e x + eval e y
  eval e (Times x y) = eval e x * eval e y
  eval e (Neg x) = negate (eval e x)

main = do
  seed <- newStdGen
  let f = trees 100 seed
      rs = f (C True 2)
      rs' = f (C False 2)
  printf "w/ depth optimisation, w/o free unary functions: %d terms, %d classes\n" (length (concat (classes rs'))) (length (classes rs'))
  printf "w/ depth optimisation: %d terms, %d classes\n" (length (concat (classes rs))) (length (classes rs))
