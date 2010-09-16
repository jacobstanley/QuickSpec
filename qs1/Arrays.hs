{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, DeriveDataTypeable #-}
module Arrays where

import Control.Monad
import Data.Typeable
import Test.QuickCheck
import Term
import System.Random

instance Arbitrary Index where arbitrary = choose (0, 15)
instance Arbitrary Array where arbitrary = fmap Array (replicateM 16 arbitrary)

instance Classify Array where
  type Value Array = Array
  evaluate = return

instance Classify Index where
  type Value Index = Index
  evaluate = return

newtype Array = Array [Int] deriving (Eq, Ord, CoArbitrary, Typeable)
newtype Index = Index Int deriving (Eq, Ord, Random, CoArbitrary, Num, Show, Typeable)

new :: Array
new = Array (replicate 16 0)

get :: Index -> Array -> Int
get (Index i) (Array xs) = xs !! i

set :: Index -> Int -> Array -> Array
set (Index i) v (Array xs) = Array (take i xs ++ [v] ++ drop (i+1) xs)
