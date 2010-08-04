{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, TypeFamilies #-}
module TestTree where

import Data.List(sort)
import Data.Ord
import Utils

-- Invariant: branches is sorted.
-- Always an infinite structure, and branches t is always a refinement
-- of t (possibly [t]).
data TestTree a = Tree { rep :: a, rest :: [a], testCase :: TestCase a, branches :: [TestTree a] }

class Ord (Result a) => Eval a where
  type TestCase a
  type Result a
  eval :: TestCase a -> a -> Result a

-- We need to use this definition of equality for the definition of
-- union below to make sense.
instance Eval a => Eq (TestTree a) where
  t1 == t2 = eval (testCase t1) (rep t1) == eval (testCase t2) (rep t2)

instance Eval a => Ord (TestTree a) where
  compare = comparing (\t -> eval (testCase t) (rep t))

tree :: Ord a => [a] -> TestCase a -> [TestTree a] -> TestTree a
tree [] _ _ = error "bug: an equivalence class can't be empty"
tree xs tc bs = Tree { rep = y, rest = ys, testCase = tc, branches = bs }
  where y:ys = sort xs

terms :: TestTree a -> [a]
terms Tree{rep = x, rest = xs} = x:xs

union :: (Ord a, Eval a) => TestTree a -> TestTree a -> TestTree a
t1 `union` t2 = tree (merge const (terms t1) (terms t2)) (testCase t1) (merge union (branches t1) (branches t2))
  where merge _ [] ys = ys
        merge _ xs [] = xs
        merge f (x:xs) (y:ys) =
          case x `compare` y of
            LT -> x:merge f xs (y:ys)
            GT -> y:merge f (x:xs) ys
            EQ -> f x y:merge f xs ys

-- Precondition: xs must be sorted.
test :: (Ord a, Eval a) => [TestCase a] -> [a] -> TestTree a
test [] xs = error "bug: ran out of test cases"
test (tc:tcs) xs = tree xs tc (map (test tcs) bs)
  where bs = partitionBy (eval tc) xs

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
