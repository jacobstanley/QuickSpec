{-# LANGUAGE ScopedTypeVariables,GeneralizedNewtypeDeriving,TypeOperators #-}
module Family where

import Control.Monad
import qualified Data.List as L
import Data.List(nub)
import System.Random
import Test.QuickCheck
import Term

-- The Ord instance can be a partial order, so x<=y,y<=x can both be False.
-- But the Eq instance ought to be valid.
class Ord a => Family a where
  intersect :: a -> a -> Maybe a
  app :: a -> a -> Maybe a
  unapp :: a -> [(a, a)]

class Ord a => WellFounded a where
  lesser1 :: a -> [a]

  lesser :: a -> [a]
  lesser x = nub (lesser' x)
    where lesser' x = x:concatMap lesser' (lesser1 x)

-- QuickCheck properties.
prop_lesser1 :: (WellFounded a, Arbitrary a) => a -> Bool
prop_lesser1 x = all (<= x) (lesser x)

prop_lesser2 :: (WellFounded a, Arbitrary a) => a -> a -> Property
prop_lesser2 x y = x <= y ==> x `elem` lesser y

prop_intersect :: (Family a, WellFounded a, Arbitrary a) => a -> a -> Property
prop_intersect x y =
  case x `intersect` y of
    Nothing -> False ==> True
    Just ixy -> property (all (ixy >=) lxy && ixy `elem` lxy)
  where lxy = lesser x `L.intersect` lesser y

prop_app :: (Family a, Arbitrary a) => a -> a -> Property
prop_app f x =
  case f `app` x of
    Nothing -> False ==> True
    Just fx -> property (f <= fx && x <= fx)

test :: forall a. (Family a, WellFounded a, Arbitrary a, Show a) => a -> IO ()
test x = do
  quickCheck (prop_lesser1 :: a -> Bool)
  quickCheck (prop_lesser2 :: a -> a -> Property)
  quickCheck (prop_intersect :: a -> a -> Property)
  quickCheck (prop_app :: a -> a -> Property)

-- Instances.

newtype Depth = Depth Int deriving (Eq, Ord, Show, Enum, Num, Random)

instance Arbitrary Depth where
  arbitrary = choose (0, 4)

instance Family Depth where
  x `intersect` y = Just (x `min` y)
  d1 `app` d2 = Just (d1 `max` (d2+1))
  unapp n = [(d1, d2) | d1 <- [0..n], d2 <- [0..n-1]]

instance WellFounded Depth where
  lesser1 x | x >= 0 = [x-1]
            | otherwise = []
  lesser x = [0..x]

newtype Size = Size Int deriving (Eq, Ord, Show, Enum, Num, Random)

instance Arbitrary Size where
  arbitrary = choose (0, 10)

instance Family Size where
  x `intersect` y = Just (x `min` y)
  x `app` y = Just (x + y)
  unapp n = [(d1, d2) | d1 <- [0..n-1], let d2 = n - d1]

instance WellFounded Size where
  lesser1 x | x >= 0 = [x-1]
            | otherwise = []
  lesser x = [0..x]

data Both a b = Both a b deriving (Eq, Show)

instance (Arbitrary a, Arbitrary b) => Arbitrary (Both a b) where
  arbitrary = liftM2 Both arbitrary arbitrary
  shrink (Both x y) = [ Both x' y | x' <- shrink x ] ++ 
                      [ Both x y' | y' <- shrink y ]

instance (Ord a, Ord b) => Ord (Both a b) where
  Both x y <= Both x' y' = x <= x' && y <= y'

instance (Family a, Family b) => Family (Both a b) where
  Both x1 x2 `intersect` Both y1 y2 = liftM2 Both (x1 `intersect` y1) (x2 `intersect` y2)
  Both f1 f2 `app` Both x1 x2 = liftM2 Both (f1 `app` x1) (f2 `app` x2)
  -- FIXME is this right?
  unapp (Both y1 y2) = [(Both f1 f2, Both x1 x2) | (f1, x1) <- unapp y1, (f2, x2) <- unapp y2]

instance (WellFounded a, WellFounded b) => WellFounded (Both a b) where
  lesser1 (Both x y) = [ Both x' y | x' <- lesser1 x ] ++ [ Both x y' | y' <- lesser1 y ]
