{-# LANGUAGE TypeFamilies #-}
module Family where

import Data.Ord

class Family f where
  intersect :: f a -> f a -> f a
  terms :: f a -> [a]

data WithBound b a = WithBound { bound :: b, terms' :: [a] }

instance Eq b => Eq (WithBound b a) where
  x == y = bound x == bound y

instance Ord b => Ord (WithBound b a) where
  compare = comparing bound

instance Ord b => Family (WithBound b) where
  intersect x y = x `min` y
  terms = terms'
