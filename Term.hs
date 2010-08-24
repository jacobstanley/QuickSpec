{-# LANGUAGE GADTs, Rank2Types, TypeFamilies, FlexibleContexts #-}
module Term where

import TestTree
import Data.Ord
import Control.Applicative

data Args f a b where
  Nil :: Args f a a
  Snoc :: Term f a -> Args f b (a -> c) -> Args f b c

instance Show (Args f a b) where
  show Nil = ""
  show (Snoc x Nil) = show x
  show (Snoc x as) = show as ++ "," ++ show x

data Term f a = forall b. App { name :: String, fun :: f b, args :: Args f b a }

-- FIXME: fix.
instance Eq (Term f a) where
  t1 == t2 = show t1 == show t2
instance Ord (Term f a) where
  compare = comparing show

instance Show (Term f a) where
  show App { name = name, args = Nil } = name
  show App { name = name, args = args } = name ++ "(" ++ show args ++ ")"

sym :: String -> f a -> Term f a
sym name fun = App { name = name, fun = fun, args = Nil }

app :: Term f (a -> b) -> Term f a -> Term f b
app App { name = name, fun = f, args = as } x = App { name = name, fun = f, args = Snoc x as }

evalTerm :: Applicative f => Term f a -> f a
evalTerm App { fun = f, args = as } = apply f as
  where apply :: Applicative f => f a -> Args f a b -> f b
        apply f Nil = f
        apply f (Snoc x as) = apply f as <*> evalTerm x
