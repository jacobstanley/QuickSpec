{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, TypeFamilies, TupleSections, ImplicitParams #-}
import Control.Monad
-- WHAT WE SHOULD DO:
-- separate testing universe from pruning universe.
-- Describe pruning universe by describing the set of all
-- substitutions of an equation instead. That way we can describe
-- the depth limit, an efficient size limit, the
-- outside-universe-by-one-step rule, the rules for bound variables,
-- the rules for conditionally-rigidified variables, etc.

-- This structure supports instance generation.
data Set tc a = Nil | Base (TestingTree tc a) | Apply (Set tc a) (Set tc a) -- | Var ...
-- Ah, so "Set a" can have the "more terms as you test more" structure
-- but TestingTree shouldn't.

-- This structure supports class refinement, union etc.
-- Invariant: branches is sorted by comparing (eval testCase . rep).
data TestingTree tc a = Tree { rep :: a, rest :: [a], testCase :: tc, branches :: [TestingTree tc a] }

class Ord (Case tc a) => TestCase tc a where
  type Case tc a
  eval :: tc -> a -> Case tc a

union :: TestCase tc a => TestingTree tc a -> TestingTree tc a -> TestingTree tc a
union t1 t2 = Tree { rep = rep t1, rest = rest t1++rep t2:rest t2, testCase = testCase t1,
                     branches = merge (branches t1) (branches t2) }
  where merge [] ys = ys
        merge xs [] = xs
        merge (x:xs) (y:ys) | eval (testCase t1) (rep t1) < eval (testCase t2) (rep t2) =
          x:merge xs (y:ys)
                            | eval (testCase t1) (rep t1) > eval (testCase t2) (rep t2) =
          y:merge (x:xs) ys
                            | otherwise = union x y:merge xs ys

partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
partitionBy = undefined

-- Precondition: xs must be sorted.
test :: TestCase tc a => [tc] -> [a] -> TestingTree tc a
test _ [] = error "bug: an equivalence class can't be empty"
test (tc:tcs) xs = Tree { rep = y, rest = ys, testCase = tc, branches = map (test tcs) (tail bs) }
  where ((y:ys):bs) = partitionBy (eval tc) xs

fringe :: TestingTree tc a -> Int
fringe = maxNumber . cutOff 0
  where cutOff 100 t = Tree { rep = rep t, rest = rest t, testCase = testCase t, branches = [] }
        cutOff n t@Tree{branches = [t']} = t { branches = [cutOff (n+1) t'] }
        cutOff n t = t { branches = map (cutOff 0) (branches t) }
        maxNumber Tree{branches = []} = 0
        maxNumber Tree{branches = bs} = 1+maximum (map maxNumber bs)
