{-# LANGUAGE TypeFamilies #-}
module Family where

import Data.Ord

data WithBound b a = WithBound { bound :: b, terms :: [a] }

instance Eq b => Eq (WithBound b a) where
  x == y = bound x == bound y

instance Ord b => Ord (WithBound b a) where
  compare = comparing bound
