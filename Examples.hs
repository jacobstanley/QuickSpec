{-# LANGUAGE ScopedTypeVariables,DeriveDataTypeable,TypeFamilies,GeneralizedNewtypeDeriving #-}

module Main where

import Equations hiding (merge)
import Term
import qualified Data.List
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
-- con "reverse" (reverse :: [Int] -> [Int]),
 con "head" (head :: [Int] -> Int),
 con "tail" (tail :: [Int] -> [Int]),
 con ":" ((:) :: Int -> [Int] -> [Int]),
 con "[]" ([] :: [Int]),
 con "sort" (Data.List.sort :: [Int] -> [Int]),
 con "mergeL" mergeL,
-- con "unit" (\x -> [x] :: [Int]),
 con "insertL" (Data.List.insert :: Int -> [Int] -> [Int]),
 con "null" (null :: [Int] -> Bool)]

mergeL :: [Int] -> [Int] -> [Int]
mergeL [] xs = xs
mergeL xs [] = xs
mergeL (x:xs) (y:ys) | x < y = x:mergeL xs (y:ys)
                    | otherwise = y:mergeL (x:xs) ys

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

toList' :: Heap a -> [a]
toList' Nil = []
toList' (Branch _ x l r) = x:(toList' l ++ toList' r)

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

leftBranch (Branch _ _ l _) = l
rightBranch (Branch _ _ _ r) = r

npl :: Heap a -> Int
npl Nil = 0
npl (Branch n _ _ _) = n

heapVars = [
 var "h" (Nil :: Heap Int),
 var "h1" (Nil :: Heap Int),
 var "h2" (Nil :: Heap Int)
 ]

heapCons = [
-- con "toList" (\h -> toList h :: [Int]),
-- con "fromList" (\xs -> fromList xs :: Heap Int),
-- con "isEmpty" (\h -> empty (h :: Heap Int)),
-- con "findMin" (\h -> top h :: Int),
 con "insert" (\x h -> insert x h :: Heap Int),
 con "deleteMin" (\h -> delete h :: Heap Int),
 con "merge" (\h1 h2 -> merge h1 h2 :: Heap Int),
 con "empty" (Nil :: Heap Int),
 con "leftBranch" (leftBranch :: Heap Int -> Heap Int),
 con "rightBranch" (rightBranch :: Heap Int -> Heap Int)
 ]

natCons = [
 con "+" ((+) :: Int -> Int -> Int),
 con "-" ((-) :: Int -> Int -> Int),
 con "*" ((*) :: Int -> Int -> Int),
 con "neg" (negate :: Int -> Int),
 con "0" (0 :: Int),
 con "1" (1 :: Int) ]

main = someLaws (baseVars ++ boolVars ++ boolCons ++ listVars ++ listCons ++ heapVars ++ heapCons) [typeOf (undefined :: Heap Int)] 3