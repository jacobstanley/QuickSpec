{-# LANGUAGE GADTs, Rank2Types, TypeFamilies, FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}
module Term where

import TestTree
import Data.Ord
import Control.Applicative
import qualified UntypedTerm as Untyped

data Args f a b where
  Nil :: Args f a a
  Snoc :: Term f a -> Args f b (a -> c) -> Args f b c

data Term f a = forall b. App { fun :: f b, args :: Args f b a }

sym :: f a -> Term f a
sym f = App { fun = f, args = Nil }

app :: Term f (a -> b) -> Term f a -> Term f b
app App { fun = f, args = as } x = App { fun = f, args = Snoc x as }

evalTerm :: forall f a. (forall a b. f (a -> b) -> f a -> f b) -> Term f a -> f a
evalTerm (<*>) App { fun = f, args = as } = apply f as
  where apply :: f b -> Args f b c -> f c
        apply f Nil = f
        apply f (Snoc x as) = apply f as <*> evalTerm (<*>) x
