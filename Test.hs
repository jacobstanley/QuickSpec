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
import Family
import UntypedTerm
import Subst hiding (Var)
import qualified Subst
import Utils
import qualified Term as T
import TermSet2

data IntTerm where
  Var :: Int -> WithBound Int IntTerm -> IntTerm
  Const :: Int -> IntTerm
  Negate :: IntTerm -> IntTerm
  Plus, Times :: IntTerm -> IntTerm -> IntTerm
  deriving Eq

instance Ord IntTerm where
  compare = comparing term

type Val = Int -> Int

trees :: [Val] -> Int -> Int -> TestResults IntTerm
trees tcs numTests = f
  where f = memo (cutOff numTests . f')
        base = memo $ \n -> test tcs $ [ Const 0, Const 1 ] ++
                                       [ x (WithBound n (reps (f n))) | x <- [Var 0, Var 1, Var 2] ]
        f' 0 = base 0
        f' (n+1) = base (n+1) `union` test tcs (liftM3 id [Plus, Times] ts ts ++ map Negate ts)
          where ts = reps (f n)

instance Eval IntTerm where
  type TestCase IntTerm = Val
  type Result IntTerm = Int
  eval val (Var n _) = val n
  eval v (Plus t u) = eval v t + eval v u
  eval v (Times t u) = eval v t * eval v u
  eval v (Negate t) = negate (eval v t)
  eval _ (Const n) = n

instance TermLike IntTerm where
  type Bound IntTerm = Int
  term (Var n b) = sym $ Subst.Var ('v':show n) b
  term (Plus t u) = App (ConstS "+") [term t, term u]
  term (Times t u) = App (ConstS "*") [term t, term u]
  term (Negate t) = App (ConstS "-") [term t]
  term (Const n) = sym $ ConstS $ show n

main = do
  seed <- newStdGen
  let rs = trees (unGen testCases seed undefined) 100 2
  printf "w/ depth optimisation: %d terms, %d classes\n" (length (concat (classes rs))) (length (classes rs))
  laws rs
