{-# LANGUAGE ScopedTypeVariables,DeriveDataTypeable,TypeFamilies #-}

module Main where

import Equations hiding (merge)
import Term
import qualified Data.List(insert)
import Data.Ord
import Data.Typeable
import Test.QuickCheck

boolVars = [
 var "x" False,
 var "y" False,
 var "z" False
 ]

boolCons = [
 con "&&" (&&),
 con "||" (||),
 con "not" not,
 con "true" True,
 con "false" False
 ]

baseVars = [
 var "x" int,
 var "y" int,
 var "z" int ]
  where int :: Int
        int = undefined

listVars = [
 var "xs" list,
 var "ys" list,
 var "zs" list ]
  where list :: [Int]
        list = undefined

listCons = [
 con "++" ((++) :: [Int] -> [Int] -> [Int]),
 con "reverse" (reverse :: [Int] -> [Int]),
 con "tail" (tail :: [Int] -> [Int]),
 con ":" ((:) :: Int -> [Int] -> [Int]),
 con "[]" ([] :: [Int]),
 con "insertL" (Data.List.insert :: Int -> [Int] -> [Int])]

-- Leftist heaps.
data Heap a = Nil | Branch Int a (Heap a) (Heap a) deriving Typeable

instance Ord a => Eq (Heap a) where
  h1 == h2 = toList h1 == toList h2

instance Ord a => Ord (Heap a) where
  compare = comparing toList

instance (Ord a, Arbitrary a) => Arbitrary (Heap a) where
  arbitrary = fmap fromList arbitrary

instance (Classify a, Ord a) => Classify (Heap a) where
  type Value (Heap a) = Heap (Value a)
  evaluate = evalMap (\f -> fromList . map f . toList)

toList :: Ord a => Heap a -> [a]
toList h | empty h = []
         | otherwise = top h:toList (delete h)

fromList :: Ord a => [a] -> Heap a
fromList = foldr insert Nil

empty :: Heap a -> Bool
empty Nil = True
empty _ = False

top :: Heap a -> a
top (Branch _ x _ _) = x

insert :: Ord a => a -> Heap a -> Heap a
insert x h = merge h (branch x Nil Nil)

delete :: Ord a => Heap a -> Heap a
delete (Branch _ _ l r) = merge l r

branch :: Ord a => a -> Heap a -> Heap a -> Heap a
branch x l r | npl l <= npl r = Branch (npl l + 1) x l r
             | otherwise = Branch (npl r + 1) x r l

merge :: Ord a => Heap a -> Heap a -> Heap a
merge Nil h = h
merge h Nil = h
merge h1@(Branch _ x1 l1 r1) h2@(Branch _ x2 l2 r2)
 | x1 <= x2 = branch x1 (merge l1 h2) r1
 | otherwise = merge h2 h1

npl :: Heap a -> Int
npl Nil = 0
npl (Branch n _ _ _) = n

heapVars = [
 var "H" (Nil :: Heap Int),
 var "H'" (Nil :: Heap Int) ]

heapCons = [
 con "toList" (\h -> toList h :: [Int]),
 con "fromList" (\xs -> fromList xs :: Heap Int),
 con "empty" (\h -> empty (h :: Heap Int)),
 con "top" (\h -> top h :: Int),
 con "insertH" (\x h -> insert x h :: Heap Int),
 con "delete" (\h -> delete h :: Heap Int),
 con "merge" (\h1 h2 -> merge h1 h2 :: Heap Int),
 con "nil" (Nil :: Heap Int)
 ]

main = someLaws (boolVars ++ boolCons ++ listVars ++ listCons ++ heapVars ++ heapCons)
                [typeOf (undefined :: Heap Int)] 3