module Utils where

import Control.Arrow((&&&))
import Data.List(groupBy, sortBy)
import Data.Ord(comparing)

partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
partitionBy value = map (map fst) . groupBy (\x y -> snd x == snd y) . sortBy (comparing snd) . map (id &&& value)
