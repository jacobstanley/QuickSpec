{-# LANGUAGE GADTs,TypeFamilies,Rank2Types,FlexibleContexts #-}

-- NOTE:
-- About imperative variables: we don't need the amusing substitution
-- consistency rules. Instead, have *one* QuickSpec variable
--   pi : Permutation
-- and selectors
--   x, y, z : Permutation -> BoundVariable
-- so that instead of writing imperative X, we write x pi.
-- There is still Big Problem Number One: how to avoid having two
-- distinct sets of variables in our program. (Just by careful term
-- generation? It's easy enough now.)
module TermSet where

import Control.Applicative hiding (Const)
import TestTree

-- WHAT WE SHOULD DO:
-- separate testing universe from pruning universe.
-- Describe pruning universe by describing the set of all
-- substitutions of an equation instead. That way we can describe
-- the depth limit, an efficient size limit, the
-- outside-universe-by-one-step rule, the rules for bound variables,
-- the rules for conditionally-rigidified variables, etc.

-- TAKE 2:
-- Define a "term with variables in" applicative. (Maybe just
-- representing an open term by a function would be OK?)

-- This structure supports instance generation.
-- data Set a = Nil | Base (TestTree a) | Apply (Set a) (Set a) -- | Var ...
-- Ah, so "Set a" can have the "more terms as you test more" structure
-- but TestingTree shouldn't.

-- Combinators such as:
--   apply
--   variable together with how to substitute for it

class Ord (Stamp v) => Variable v where
  type Stamp v
  intersect :: v a -> v a -> v a

-- The main data structure is a TestTree (Term v a).
--
-- (We can do: given t, generate all t[v/x]. But also need to be able to generate u[v/x] for the instance generation. Does this work? Probably yes, although we might have to just write our own function for doing it instead of using "interpret".
--
-- Also, need to be able to make sure that e.g. with x+x, we instantiate it to 0+0 and 1+1 but not 0+1, i.e., all copies of a variable must be instantiated to the same thing.)
data Term v a where
  Var :: Variable v => v a -> Term v a
  Const :: a -> Term v a
  Ap :: Term v (a -> b) -> Term v a -> Term v b

interpret :: (forall a. v a -> a) -> Set v a -> [a]
interpret values (Var v) = values v
interpret values (Const xs) = xs
interpret values (Ap f x) = interpret values f <*> interpret values x

-- All this clever stuff is probably unnecessary. Just need each term
-- to be packaged up with a list of substitutions, and combinators for
-- the description thereof :P
