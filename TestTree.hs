{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, TypeFamilies #-}
module TestTree(Eval(..), TestTree, terms, union, test,
               filter, TestResults, cutOff, numTests, classes, reps) where

import Prelude hiding (filter)
import Data.List(sort)
import Data.Ord
import Utils
import Control.Exception(assert)

-- Invariant: the children of a TestTree are sorted according to the
-- parent's testCase. We exploit this in defining merge.
-- 
-- A TestTree is always infinite, and branches t is always a
-- refinement of t (it may be trivial, so that length (branches t) == 1).
data TestTree a = Tree { rep :: a, rest :: [a], testCase :: TestCase a, branches :: [TestTree a] }

class Ord (Result a) => Eval a where
  type TestCase a
  type Result a
  eval :: TestCase a -> a -> Result a

-- Precondition: xs must be sorted, and bs must be sorted according to
-- the TestCase.
tree :: (Ord a, Eval a) => [a] -> TestCase a -> [TestTree a] -> TestTree a
tree [] _ _ = error "bug: an equivalence class can't be empty"
tree (x:xs) tc bs =
  assert (isSortedBy (eval tc . rep) bs) $
  assert (isSorted xs) $
    Tree { rep = x, rest = xs, testCase = tc, branches = bs }

terms :: TestTree a -> [a]
terms Tree{rep = x, rest = xs} = x:xs

union :: (Ord a, Eval a) => TestTree a -> TestTree a -> TestTree a
t1 `union` t2 =
  tree (merge const id (terms t1) (terms t2)) (testCase t1)
       (merge union (eval (testCase t1) . rep) (branches t1) (branches t2))

merge :: Ord b => (a -> a -> a) -> (a -> b) -> [a] -> [a] -> [a]
merge _ _ [] ys = ys
merge _ _ xs [] = xs
merge f c (x:xs) (y:ys) =
  case comparing c x y of
    LT -> x:merge f c xs (y:ys)
    GT -> y:merge f c (x:xs) ys
    EQ -> f x y:merge f c xs ys

test :: (Ord a, Eval a) => [TestCase a] -> [a] -> TestTree a
test tcs xs = test' tcs (sort xs)

-- Precondition: the list of terms must be sorted.
test' :: (Ord a, Eval a) => [TestCase a] -> [a] -> TestTree a
test' [] xs = error "bug: ran out of test cases"
test' (tc:tcs) xs = assert (isSorted xs) $
                   -- Too clever by half trick (hence the above assert):
                   -- sort is stable, so each b <- bs is sorted
                   -- according to the usual Ord order.
                   tree xs tc (map (test' tcs) bs)
  where bs = partitionBy (eval tc) xs

-- Ignore some testcases (useful for conditional equations?)
filter :: (Ord a, Eval a) => (TestCase a -> Bool) -> TestTree a -> TestTree a
filter p t | p (testCase t) = t { branches = bs }
           | otherwise = foldr1 union bs
  where bs = map (filter p) (branches t)

-- A TestTree with finite depth, represented as a TestTree where some
-- nodes have no branches. Since this breaks one of the TestTree
-- invariants we use a different type.
newtype TestResults a = Results (TestTree a)

cutOff :: Int -> TestTree a -> TestResults a
cutOff n = Results . aux n
  where aux 0 t = t { branches = [] }
        aux m t@Tree{branches = [t']} = t { branches = [aux (m-1) t'] }
        aux m t = t { branches = map (aux n) (branches t) }

numTests :: TestResults a -> Int
numTests (Results t) = aux t
  where aux Tree{branches = []} = 0
        aux Tree{branches = bs} = 1 + maximum (map aux bs)

classes :: TestResults a -> [[a]]
classes (Results t) = aux t
  where aux Tree{rep = x, rest = xs, branches = []} = [x:xs]
        aux Tree{branches = bs} = concatMap aux bs

reps :: TestResults a -> [a]
reps = map head . classes
