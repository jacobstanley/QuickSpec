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

type Val = [Int]

trees :: [Val] -> Int -> Int -> TestResults IntTerm
trees tcs numTests = f
  where f = memo (cutOff numTests . f')
        base = memo $ \n -> test tcs $ [ Const 0, Const 1 ] ++
                                       [ x (WithBound n (reps (f n))) | x <- [Var 0, Var 1, Var 2] ]
        f' 0 = base 0
        f' (n+1) = base (n+1) `union` test tcs (liftM3 id [Plus, Times] ts ts ++ map Negate ts)
          where ts = reps (f n)

base0 = set 0 {- family -} [Const 0, Const 1] -- something like Set Int IntTerm
base1 = set 0 [Negate] -- Set Int (IntTerm -> IntTerm)
base2 = set 0 [Plus, Times] -- Set Int (IntTerm -> IntTerm IntTerm)
terms 0 = base0
terms (n+1) = base0 `union` base1 <*> terms n `union` base2 <*> terms n <*> terms n
-- instance Family f => Applicative (Set f) where ...
-- pure produces something of depth 0
-- <*> uses family apply?? does this respect the arrow rules?
-- pure f <*> x = fmap f x
-- in particular, pure id <*> x = x which is not really respected when family is depth
-- (maybe we don't even want it to be a Functor...)

-- maybe we can also specify a "variable mapping" depth -> [Var] so that a variable can represent several depths, rather than generating WithBound nonsense as we go.
-- Our term-generation data structure will be a map family -> TestTree blahblah.
-- So then we aggressively split up our termsets by family?
-- We also need some stuff so that a family can include smaller families---implementation: memoise a function [Family]->TestTree. Alternatively---when we see a variable in a term, we remember which other terms we could have generated there. What we're proposing now is to reconstruct the variable's family later instead, which is maybe not as nice... because, what we have is the depth of the term as a whole and not the depth of the "hole" that the variable fills.

instance Eval IntTerm where
  type TestCase IntTerm = Val
  type Result IntTerm = Int
  eval val (Var n _) = val !! n
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
  let rs = trees (unGen (testCases (repeatM arbitrary)) seed undefined) 100 2
  printf "w/ depth optimisation: %d terms, %d classes\n" (length (concat (classes rs))) (length (classes rs))
  laws rs
