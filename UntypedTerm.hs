module UntypedTerm where

import Data.List
import Data.Ord

data Term a = App { fun :: a, revArgs :: [Term a] } deriving Eq

args :: Term a -> [Term a]
args = reverse . revArgs

instance Ord a => Ord (Term a) where
  compare = comparing stamp
    where stamp t = (depth t, size t, fun t, args t)
          depth App { revArgs = [] } = 0 :: Int
          depth App { revArgs = ts } = 1 + maximum (map depth ts)
          size App { revArgs = ts } = 1 + sum (map size ts) :: Int

instance Show a => Show (Term a) where
  show (App { fun = f, revArgs = [] }) = show f
  show (App { fun = f, revArgs = xs }) = show f ++ "(" ++ intercalate "," (map show (reverse xs)) ++ ")"

sym :: a -> Term a
sym f = App { fun = f, revArgs = [] }

app :: Term a -> Term a -> Term a
app App { fun = f, revArgs = as } x = App { fun = f, revArgs = x:as }

