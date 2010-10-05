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

data BoolTerm where
  X, Y, Z :: WithBound Int BoolTerm -> BoolTerm
  P1 :: BoolTerm
  P2 :: BoolTerm
  Const :: Bool -> BoolTerm
  Not :: BoolTerm -> BoolTerm
  And, Or :: BoolTerm -> BoolTerm -> BoolTerm
  deriving Eq

data Type a where
  Arr :: Type a -> Type b -> Type (a -> b)
  Bool :: Type Bool

instance Ord BoolTerm where
  compare = comparing term

type Val = (Bool, Bool, Bool, Bool)

tests :: StdGen -> [Val]
tests g = unGen (repeatM arbitrary) g 5

type Fun = (->)

trees :: [Val] -> Int -> Int -> TestResults BoolTerm
trees tcs numTests = f
  where f = memo (cutOff numTests . f')
        base = memo $ \n -> test tcs $ [ Const False, Const True, P1, P2 ] ++
                                       [ x (WithBound n (reps (f n))) | x <- [X, Y, Z] ]
        f' 0 = base 0
        f' (n+1) = base (n+1) `union` test tcs (liftM3 id [And, Or] ts ts ++ map Not ts)
          where ts = reps (f n)

instance Eval BoolTerm where
  type TestCase BoolTerm = Val
  type Result BoolTerm = Bool
  eval (x,_,_,_) (X _) = x
  eval (_,y,_,_) (Y _) = y
  eval (_,_,z,_) (Z _) = z
  eval (_,_,_,p) P1 = p
  eval (_,_,_,p) P2 = not p
  eval v (And t u) = eval v t && eval v u
  eval v (Or t u) = eval v t || eval v u
  eval v (Not t) = not (eval v t)
  eval _ (Const x) = x

instance TermLike BoolTerm where
  type Bound BoolTerm = Int
  term (X b) = sym $ Var "x" b
  term (Y b) = sym $ Var "y" b
  term (Z b) = sym $ Var "z" b
  term P1 = sym $ ConstS "p1"
  term P2 = sym $ ConstS "p2"
  term (And t u) = App (ConstS "&&") [term t, term u]
  term (Or t u) = App (ConstS "||") [term t, term u]
  term (Not t) = App (ConstS "not") [term t]
  term (Const n) = sym $ ConstS $ show n

main = do
  seed <- newStdGen
  let rs = trees (tests seed) 100 2
  printf "w/ depth optimisation: %d terms, %d classes\n" (length (concat (classes rs))) (length (classes rs))
  laws rs
