{-# LANGUAGE GADTs, Rank2Types, TypeFamilies #-}
module Term where

import TestTree

data Args v a b where
  Nil :: Args v a a
  Snoc :: Term v a -> Args v b (a -> c) -> Args v b c

data Term v a = forall b. App { name :: String, fun :: (v -> b), args :: Args v b a }

sym :: String -> (v -> a) -> Term v a
sym name fun = App { name = name, fun = fun, args = Nil }

app :: Term v (a -> b) -> Term v a -> Term v b
app App { name = name, fun = f, args = as } x = App { name = name, fun = f, args = Snoc x as }

evalTerm :: v -> Term v a -> a
evalTerm v App { fun = f, args = as } = apply v (f v) as
  where apply :: v -> a -> Args v a b -> b
        apply v f Nil = f
        apply v f (Snoc x as) = apply v f as (evalTerm v x)

instance Ord a => Eval (Term v a) where
  type Result (Term v a) = a
  type TestCase (Term v a) = v
  eval = evalTerm
