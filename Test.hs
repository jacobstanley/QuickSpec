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
import Subst
import Utils
import qualified Term as T

data IntTerm where
  X, Y, Z :: WithBound Int IntTerm -> IntTerm
  Const :: Int -> IntTerm
  Negate :: IntTerm -> IntTerm
  Plus, Times :: IntTerm -> IntTerm -> IntTerm
  deriving Eq

data IntSym a where
  SX, SY, SZ :: WithBound Int (T.Term IntSym a) -> IntSym a
  SConst :: a -> IntSym a
  SNegate :: IntSym (Int -> Int)
  SPlus, STimes :: IntSym (Int -> Int -> Int)

data Type a where
  Arr :: Type a -> Type b -> Type (a -> b)
  Int :: Type Int

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

main = do
  seed <- newStdGen
  let rs = trees (tests seed) 100 2
  printf "w/ depth optimisation: %d terms, %d classes\n" (length (concat (classes rs))) (length (classes rs))
  laws rs
