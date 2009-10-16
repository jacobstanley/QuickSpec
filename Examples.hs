{-# LANGUAGE ScopedTypeVariables,DeriveDataTypeable,TypeFamilies,GeneralizedNewtypeDeriving,TypeSynonymInstances,StandaloneDeriving #-}

module Main where

import Equations hiding (merge, evaluate)
import Term
import qualified Data.List
import Data.Ord
import Data.Typeable
import Test.QuickCheck
import System
import System.Random
import Control.Monad
import Control.Monad.State

bools = describe "bools" [
 var "x" False,
 var "y" False,
 var "z" False,
 con "&&" (&&),
 con "||" (||),
 con "not" not,
 con "true" True,
 con "false" False
 ]

base = [
 var "x" int,
 var "y" int,
 var "z" int ]
  where int :: Int
        int = undefined

lists = describe "lists" [
 var "xs" list,
 var "ys" list,
 var "zs" list,
 con "++" ((++) :: [Int] -> [Int] -> [Int]),
 con "reverse" (reverse :: [Int] -> [Int]),
 con "head" (head :: [Int] -> Int),
 con "tail" (tail :: [Int] -> [Int]),
 con ":" ((:) :: Int -> [Int] -> [Int]),
 con "[]" ([] :: [Int]),
 con "sort" (Data.List.sort :: [Int] -> [Int]),
 con "mergeL" mergeL,
 con "unit" (\x -> [x] :: [Int]),
 con "insertL" (Data.List.insert :: Int -> [Int] -> [Int]),
 con "null" (null :: [Int] -> Bool)]
  where list :: [Int]
        list = undefined

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
  type Value (Heap a) = [Value a]
  evaluate = evaluate . toList

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

heaps = describe "heaps" [
 var "h" (Nil :: Heap Int),
 var "h1" (Nil :: Heap Int),
 var "h2" (Nil :: Heap Int),
 con "toList" (\h -> toList h :: [Int]),
 con "fromList" (\xs -> fromList xs :: Heap Int),
 con "isEmpty" (\h -> empty (h :: Heap Int)),
 con "findMin" (\h -> top h :: Int),
 con "insert" (\x h -> insert x h :: Heap Int),
 con "deleteMin" (\h -> delete h :: Heap Int),
 con "merge" (\h1 h2 -> merge h1 h2 :: Heap Int),
 con "empty" (Nil :: Heap Int)
-- con "leftBranch" (leftBranch :: Heap Int -> Heap Int),
-- con "rightBranch" (rightBranch :: Heap Int -> Heap Int)
 ]

nats = describe "nats" [
 con "+" ((+) :: Int -> Int -> Int),
 con "-" ((-) :: Int -> Int -> Int),
 con "*" ((*) :: Int -> Int -> Int),
 con "neg" (negate :: Int -> Int),
 con "0" (0 :: Int),
 con "1" (1 :: Int) ]

examples = [
 ("nats", (base ++ nats, allOfThem)),
 ("bools", (base ++ bools, allOfThem)),
 ("lists", (base ++ bools ++ lists, about ["lists"])),
 ("heaps", (base ++ bools ++ lists ++ heaps, about ["heaps"])),
 ("arrays", (base ++ arrays, allOfThem)),
 ("comp", (base ++ comp, allOfThem)),
 ("queues", (base ++ queues ++ bools, about ["queues"]))
 ]

main = do
  args <- getArgs
  let test = case args of
               [] -> "bools"
               [x] -> x
      Just (cons, p) = lookup test examples
  laws 3 cons p

newtype Index = Index Int deriving (Eq, Ord, CoArbitrary, Random, Num, Show, Typeable)
instance Arbitrary Index where arbitrary = choose (0, 15)
newtype Array = Array [Int] deriving (Eq, Ord, CoArbitrary, Typeable)
instance Arbitrary Array where arbitrary = fmap Array (replicateM 16 arbitrary)

instance Classify Array where
  type Value Array = Array
  evaluate = return

instance Classify Index where
  type Value Index = Index
  evaluate = return

arrays = [
 var "a" (Array undefined),
 var "i" (Index undefined),
 var "j" (Index undefined),
 var "k" (Index undefined),
 con "new" (Array (replicate 16 0)),
 con "get" (\(Index ix) (Array a) -> a !! ix),
 con "set" (\(Index ix) v (Array a) -> Array [ if i == ix then v else a !! i | i <- [0..15] ]),
 con "0" (0 :: Int)
 ]

comp = [
 var "f" (undefined :: (Int -> Int)),
 var "g" (undefined :: (Int -> Int)),
 var "h" (undefined :: (Int -> Int)),
 con "." (\f g x -> f (g (x :: Int) :: Int) :: Int),
 con "id" (id :: Int -> Int)]

data Queue = Queue [Int] [Int] deriving Typeable

instance Eq Queue where
  q1 == q2 = q1 `compare` q2 == EQ

instance Ord Queue where
  compare = comparing listQ

instance Arbitrary Queue where
  arbitrary = liftM2 Queue arbitrary arbitrary

deriving instance Typeable2 State

listQ (Queue xs ys) = xs ++ reverse ys

new = Queue [] []
nullQ (Queue [] []) = True
nullQ _ = False

inl x (Queue xs ys) = Queue (x:xs) ys
inr y (Queue xs ys) = Queue xs (y:ys)
outl = withLeft (\(x:xs) ys -> Queue xs ys)
outr = withRight (\xs (y:ys) -> Queue xs ys)
peekl = withLeft (\(x:xs) ys -> x)
peekr = withRight (\xs (y:ys) -> y)
withLeft f (Queue [] ys) = f (reverse ys) []
withLeft f (Queue xs ys) = f xs ys
withRight f (Queue xs []) = f [] (reverse xs)
withRight f (Queue xs ys) = f xs ys

type QueueM a = State Queue a

instance Classify a => Classify (QueueM a) where
  type Value (QueueM a) = (Value a, Queue)
  evaluate m = do
    q <- arbitrary
    let (x, q') = runState m q
    x' <- evaluate x
    return (x', q')

instance Classify () where
  type Value () = ()
  evaluate = return

newM :: QueueM ()
newM = put new

nullM :: QueueM Bool
nullM = gets nullQ

inlM, inrM :: Int -> QueueM ()
inlM x = modify (inl x)
inrM x = modify (inr x)

outlM, outrM :: QueueM ()
outlM = modify outl
outrM = modify outr

peeklM, peekrM :: QueueM Int
peeklM = gets peekl
peekrM = gets peekr

queues = describe "queues" [
 con "new" newM,
 con "null" nullM,
 con "inl" inlM,
 con "inr" inrM,
 con "outl" outlM,
 con "outr" outrM,
 con "peekl" peeklM,
 con "peekr" peekrM,
 con "()" ()
 ]