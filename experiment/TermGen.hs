module TermGen where

import Data.MemoTrie
import Family
import Term

type TermSet ty = ty -> [[Term Symbol]]
type Environment ty = Symbol -> ty

reps :: TermSet ty -> ty -> [Term Symbol]
reps s = map head . s

terms :: TermSet ty -> ty -> [Term Symbol]
terms s = concat . s

computeTerms :: Family ty => TermSet ty -> ty -> [Term Symbol]
computeTerms = undefined

instances :: Family ty => Environment ty -> Term Symbol -> [(Symbol, ty)]
instances = undefined

upToType :: Family ty => ty -> TermSet ty -> [Term Symbol]
upToType ty s = concatMap (terms s) (closure ty)

closure :: Family ty => [ty] -> [ty]
closure = undefined
-- ooh, "closure of a set of terms" and "terms built from
-- representatives+alpha-renamings" are both best-expressed using some
-- mythical "closed set" data structure
