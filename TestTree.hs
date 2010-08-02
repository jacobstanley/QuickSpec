{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, TypeFamilies #-}
module TestTree where

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

union :: TestCase tc a => TestTree tc a -> TestTree tc a -> TestTree tc a
-- FIXME: make sure that rep always becomes the one we want, including
-- in "test".
union t1 t2 = Tree { rep = rep t1, rest = rest t1++rep t2:rest t2, testCase = testCase t1,
                     branches = merge (branches t1) (branches t2) }
  where [] `merge` ys = ys
        xs `merge` [] = xs
        (x:xs) `merge` (y:ys) =
          case x `compare` y of
            LT -> x:merge xs (y:ys)
            GT -> y:merge (x:xs) ys
            EQ -> x `union` y:xs `merge` ys

-- Precondition: xs must be sorted.
test :: TestCase tc a => [tc] -> [a] -> TestTree tc a
test _ [] = error "bug: an equivalence class can't be empty"
test (tc:tcs) (x:xs) = Tree { rep = x, rest = xs, testCase = tc, branches = map (test tcs) bs }
  where bs = partitionBy (eval tc) (x:xs)

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
