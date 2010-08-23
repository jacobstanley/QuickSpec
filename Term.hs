{-# LANGUAGE GADTs, Rank2Types, TypeFamilies, FlexibleContexts #-}
module Term where

import TestTree
import Data.Ord

data Args v a b where
  Nil :: Args v a a
  Snoc :: Term v a -> Args v b (a -> c) -> Args v b c

instance Show (Args v a b) where
  show Nil = ""
  show (Snoc x Nil) = show x
  show (Snoc x as) = show as ++ "," ++ show x

data Term v a = forall b. App { name :: String, fun :: (v -> b), args :: Args v b a }

class Ord (Observation a) => Observe a where
  type Context a
  type Observation a
  observe :: Context a -> a -> Observation a

instance Eq (Term v a) where
  t1 == t2 = show t1 == show t2
instance Ord (Term v a) where
  compare = comparing show

instance Show (Term v a) where
  show App { name = name, args = Nil } = name
  show App { name = name, args = args } = name ++ "(" ++ show args ++ ")"

sym :: String -> (v -> a) -> Term v a
sym name fun = App { name = name, fun = fun, args = Nil }

app :: Term v (a -> b) -> Term v a -> Term v b
app App { name = name, fun = f, args = as } x = App { name = name, fun = f, args = Snoc x as }

evalTerm :: v -> Term v a -> a
evalTerm v App { fun = f, args = as } = apply v (f v) as
  where apply :: v -> a -> Args v a b -> b
        apply v f Nil = f
        apply v f (Snoc x as) = apply v f as (evalTerm v x)

-- FIXME: maybe it would be better to have a different ObservedTerm
-- type and use it in testing instead.
instance Observe a => Eval (Term v a) where
  type Result (Term v a) = Observation a
  type TestCase (Term v a) = (Context a, v)
  eval (c, v) t = observe c (evalTerm v t)
