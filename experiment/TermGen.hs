{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, TypeOperators #-}
module TermGen where

import Control.Monad
import Data.MemoTrie
import Data.Typeable
import Control.Arrow((***))
import Data.List hiding (intersect, and)
import Prelude hiding (and)
import Data.Maybe

data Term fam = Var Int fam | Const String fam | App (Term fam) (Term fam) deriving Show

class HasTrie fam => Family fam where
  app :: fam -> fam -> Maybe fam
  lessEq :: fam -> fam -> Bool

data Typed fam where
  --- like fam but with type information added

instance Family fam => Family (Typed fam) where
  -- ...

newtype Nat = Nat Integer deriving (Eq, Ord, Num, Enum)
instance Show Nat where
  show (Nat x) = show x

instance HasTrie Nat where
  newtype Nat :->: a = NatTrie (Integer :->: a)
  trie f = NatTrie (trie (f . Nat))
  untrie (NatTrie t) (Nat x) = untrie t x
  enumerate t = [(i, untrie t i) | i <- [0..]]

newtype Depth = Depth Nat deriving (Eq, Ord, Show)

instance HasTrie Depth where
  newtype Depth :->: a = DepthTrie (Nat :->: a)
  trie f = DepthTrie (trie (f . Depth))
  untrie (DepthTrie t) (Depth x) = untrie t x
  enumerate (DepthTrie t) = map (Depth *** id) (enumerate t)

instance Family Depth where
  app (Depth x) (Depth y) = Just (Depth (x `max` (y+1)))
  split (Depth n) = [(Depth n, Depth i) | i <- [0..n-1]] ++ [(Depth i, Depth (n-1)) | i <- [0..n-1]]
  intersect (Depth x) (Depth y) = Just (Depth (x `min` y))
  lessEq (Depth x) (Depth y) = x <= y
  lower (Depth 0) = []
  lower (Depth n) = [Depth (n-1)]

newtype Size = Size Nat deriving (Eq, Ord, Show)

instance HasTrie Size where
  newtype Size :->: a = SizeTrie (Nat :->: a)
  trie f = SizeTrie (trie (f . Size))
  untrie (SizeTrie t) (Size x) = untrie t x
  enumerate (SizeTrie t) = map (Size *** id) (enumerate t)

instance Family Size where
  app (Size x) (Size y) = Just (Size (x+y))
  split (Size n) = [(Size i, Size j) | i <- [0..n-1], let j = n - i]
  intersect (Size x) (Size y) = Just (Size (x `min` y))
  lessEq (Size x) (Size y) = x <= y
  lower (Size 0) = []
  lower (Size n) = [Size (n-1)]

instance (Family a, Family b) => Family (a, b) where
  app (x1, x2) (y1, y2) = do
    z1 <- app x1 y1
    z2 <- app x2 y2
    return (z1, z2)
  split (z1, z2) = [((x1, x2), (y1, y2)) | (x1, y1) <- split z1, (x2, y2) <- split z2]
  intersect (x1, x2) (y1, y2) = do
    z1 <- intersect x1 y1
    z2 <- intersect x2 y2
    return (z1, z2)
  lessEq (x1, x2) (y1, y2) = x1 <= y1 && x2 <= y2
  lower (x, y) = [(x', y) | x' <- lower x] ++ [(x, y') | y' <- lower y]

data TermSet fam = TermSet {
  --closure :: fam -> [fam],
  environment :: fam -> [Term fam],
  terms :: fam -> [Term fam]
  }

measure :: Family fam => Term fam -> Maybe fam
measure (Var _ fam) = Just fam
measure (Const _ fam) = Just fam
measure (App f x) = join (liftM2 app (measure f) (measure x))

-- all terms that are of exactly this type?
allTerms :: Family fam => [Term fam] -> fam -> [Term fam]
allTerms env fam = [ t | t <- env, measure t == Just fam ] ++
                   [ App f x | (famf, famx) <- split fam, -- this doesn't quite work with types as families
                                                          -- maybe just pass the env to split?
                               f <- allTerms env famf,
                               x <- allTerms env famx ]

-- all instances up to this type
-- we don't necessarily need to produce a list, rather a substitution
-- function...
-- So better would be
-- subst = {(var, maxfam, fam -> subst)}
-- don't forget that instances is called very seldom---only when we
-- have a new law. so doesn't need to be blisteringly quick.
-- even---term -> var -> [fam].
-- substitute the fam for the var in the term, carry on with the next
-- variable.
-- Then we don't need split at all(?)---we can just enumerate all fams
-- that might work (since there's no nasty exponential blowup).
-- (Well, we might get some blowup with combinations like (Depth,
-- Size, FreeVars.)
-- (Yes, FreeVars leads to blowup because we have 3*#types variables.)
--
-- OK, so we need to know very easily which types are empty and not
-- even consider them---means building terms bottom-up. That's a nice
-- way because it only requires implementing app and not split.
instances :: Family fam => fam -> Term fam -> [[((Int, fam), fam)]]
instances fam (Var v f) | f `lessEq` fam = [[((v, f), fam)]]
                        | otherwise = []
instances fam (Const c _) = [[]]
instances fam (App f x) = nubSort $ do
  (fam1, fam2) <- split fam
  cs1 <- instances fam1 f
  cs2 <- instances fam2 x
  maybeToList (merge cs1 cs2)

closure :: Family fam => [fam] -> [fam]
closure fam | fam == fam' = fam
            | otherwise = closure fam'
  where fam' = nubSort (fam ++ concatMap lower fam)

nubSort :: Ord a => [a] -> [a]
nubSort = map head . group . sort

merge :: Family fam => [((Int, fam), fam)] -> [((Int, fam), fam)] -> Maybe [((Int, fam), fam)]
merge xs [] = Just xs
merge [] ys = Just ys
merge ((x,xc):xs) ((y,yc):ys) | x < y = fmap ((x,xc):) (merge xs ((y,yc):ys))
                              | y < x = fmap ((y,yc):) (merge ((x,xc):xs) ys)
                              | x == y = do
                                c <- xc `intersect` yc
                                fmap ((x,c):) (merge xs ys)

base = (Depth 0, Size 1)
x = Var 0 base
y = Var 1 base
z = Var 2 base
and t u = App (App (Const "&&" base) t) u
t = and x (and y z)

base' = Depth 0
x' = Var 0 base'
y' = Var 1 base'
z' = Var 2 base'
and' t u = App (App (Const "&&" base') t) u
t' = and' x' (and' y' z')

--instances :: Family ty => Environment ty -> ty -> Term Symbol -> [[(Symbol, ty)]]
--instances env ty (Var v) = [[(v, ty')] | ty' <- closure [ty]]
--instances env (Const c) = []
--instances env (App f x) = undefined

--upToType :: Family ty => ty -> TermSet ty -> [Term Symbol]
--upToType ty s = concatMap (terms s) (closure [ty])

--findType :: Family ty => Environment ty -> Term Symbol -> Maybe ty
--findType env (Var v) = Just (env v)
--findType env (Const c) = Just (env c)
--findType env (App f x) = join (liftM2 app (findType env f) (findType env x))

--closure :: Family ty => [ty] -> [ty]
--closure = undefined

-- ooh, "closure of a set of terms" and "terms built from
-- representatives+alpha-renamings" are both best-expressed using some
-- mythical "closed set" data structure

-- For depth optimisation, without weirdness, give a hierarchy of
-- constraint-set and apply each constraint at once.
-- So function constraint -> "universe".
-- Makes memoisation work well---e.g., terms of the same depth will
-- all be tested at the same time.
-- Can we calculate the hierarchy automatically?
-- Wanted with hierarchy:
--   no duplication of efforts---a < b, a < c, b < d, c < d---group b
--     and c into same level, since they'll both include a.
--   no "baby steps" of refinement since we can't incrementally add
--   terms---or maybe we should be able to incrementally add terms
-- We need: if a term is a representative in its hierarchy, it's
-- always a representative. Means: If h1 <= h2, t \notin h1, t \in h2
-- then t is not less than any term in h1.
