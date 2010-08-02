{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, TypeFamilies, TupleSections, ImplicitParams #-}
module TestTree where

import Utils

-- This structure supports class refinement, union etc.
-- Invariant: branches is sorted by comparing (eval testCase . rep).
data TestTree tc a = Tree { rep :: a, rest :: [a], testCase :: tc, branches :: [TestTree tc a] }

class Ord (Case tc a) => TestCase tc a where
  type Case tc a
  eval :: tc -> a -> Case tc a

union :: TestCase tc a => TestTree tc a -> TestTree tc a -> TestTree tc a
union t1 t2 = Tree { rep = rep t1, rest = rest t1++rep t2:rest t2, testCase = testCase t1,
                     branches = merge (branches t1) (branches t2) }
  where merge [] ys = ys
        merge xs [] = xs
        merge (x:xs) (y:ys) | eval (testCase t1) (rep t1) < eval (testCase t2) (rep t2) = x:merge xs (y:ys)
                            | eval (testCase t1) (rep t1) > eval (testCase t2) (rep t2) = y:merge (x:xs) ys
                            | otherwise = union x y:merge xs ys

-- Precondition: xs must be sorted.
test :: TestCase tc a => [tc] -> [a] -> TestTree tc a
test _ [] = error "bug: an equivalence class can't be empty"
test (tc:tcs) (x:xs) = Tree { rep = x, rest = xs, testCase = tc, branches = map (test tcs) bs }
  where bs = partitionBy (eval tc) (x:xs)

fringe :: TestTree tc a -> Int
fringe = maxNumber . cutOff 0
  where cutOff 100 t = Tree { rep = rep t, rest = rest t, testCase = testCase t, branches = [] }
        cutOff n t@Tree{branches = [t']} = t { branches = [cutOff (n+1) t'] }
        cutOff n t = t { branches = map (cutOff 0) (branches t) }
        maxNumber Tree{branches = []} = 0
        maxNumber Tree{branches = bs} = 1+maximum (map maxNumber bs)
