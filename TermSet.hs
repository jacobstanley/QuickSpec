module TermSet where

import TestTree

-- WHAT WE SHOULD DO:
-- separate testing universe from pruning universe.
-- Describe pruning universe by describing the set of all
-- substitutions of an equation instead. That way we can describe
-- the depth limit, an efficient size limit, the
-- outside-universe-by-one-step rule, the rules for bound variables,
-- the rules for conditionally-rigidified variables, etc.

-- This structure supports instance generation.
data Set tc a = Nil | Base (TestTree tc a) | Apply (Set tc a) (Set tc a) -- | Var ...
-- Ah, so "Set a" can have the "more terms as you test more" structure
-- but TestingTree shouldn't.
