{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, TypeFamilies #-}
module TestTree where

import Data.List(sort)
import Data.Ord
import Utils

-- Invariant: branches is sorted.
-- Always an infinite structure, and branches t is always a refinement
-- of t (possibly [t]).
data TestTree tc a = Tree { rep :: a, rest :: [a], testCase :: tc, branches :: [TestTree tc a] }

class Ord (Case tc a) => TestCase tc a where
  type Case tc a
  eval :: tc -> a -> Case tc a

-- We need to use this definition of equality for the definition of
-- union below to make sense.
instance TestCase tc a => Eq (TestTree tc a) where
  t1 == t2 = eval (testCase t1) (rep t1) == eval (testCase t2) (rep t2)

instance TestCase tc a => Ord (TestTree tc a) where
  compare = comparing (\t -> eval (testCase t) (rep t))

tree :: Ord a => [a] -> tc -> [TestTree tc a] -> TestTree tc a
tree [] _ _ = error "bug: an equivalence class can't be empty"
tree xs tc bs = Tree { rep = y, rest = ys, testCase = tc, branches = bs }
  where y:ys = sort xs

terms :: TestTree tc a -> [a]
terms Tree{rep = x, rest = xs} = x:xs

union :: (Ord a, TestCase tc a) => TestTree tc a -> TestTree tc a -> TestTree tc a
t1 `union` t2 = tree (merge const (terms t1) (terms t2)) (testCase t1) (merge union (branches t1) (branches t2))
  where merge _ [] ys = ys
        merge _ xs [] = xs
        merge f (x:xs) (y:ys) =
          case x `compare` y of
            LT -> x:merge f xs (y:ys)
            GT -> y:merge f (x:xs) ys
            EQ -> f x y:merge f xs ys

-- Precondition: xs must be sorted.
test :: (Ord a, TestCase tc a) => [tc] -> [a] -> TestTree tc a
test [] xs = error "bug: ran out of test cases"
test (tc:tcs) xs = tree xs tc (map (test tcs) bs)
  where bs = partitionBy (eval tc) xs

-- A TestTree with finite depth, represented as a TestTree where some
-- nodes have no branches. Since this breaks one of the TestTree
-- invariants we use a different type.
newtype TestResults tc a = Results (TestTree tc a)

cutOff :: Int -> TestTree tc a -> TestResults tc a
cutOff n = Results . aux n
  where aux 0 t = t { branches = [] }
        aux m t = t { branches = map (aux (m-1)) (branches t) }

numTests :: TestResults tc a -> Int
numTests (Results t) = aux t
  where aux Tree{branches = []} = 0
        aux Tree{branches = bs} = 1 + maximum (map aux bs)

classes :: TestResults tc a -> [[a]]
classes (Results t) = aux t
  where aux Tree{rep = x, rest = xs, branches = []} = [x:xs]
        aux Tree{branches = bs} = concatMap aux bs
