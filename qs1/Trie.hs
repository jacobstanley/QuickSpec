{-# LANGUAGE TypeFamilies,FlexibleContexts #-}
module Trie where

import Data.Array
import Data.Monoid

class Ix a => FiniteIx a where
    maxRange :: a -> (a, a)

class (FiniteIx (Base a)) => Flat a where
    type Base a
    flatten :: a -> [Base a]

data Trie k a = Single a | Trie (Array (Base k) (Trie k a)) a

nil :: Monoid a => Trie k a
nil = Single mempty

root :: Monoid a => Trie k a -> a
root (Single x) = x
root (Trie _ x) = x

path :: (Flat k, Monoid a) => [Base k] -> Trie k a -> Trie k a
path [] t = t
path (k:ks) (Trie a _) = path ks (a ! k)
path _ _ = nil

lookup :: (Flat k, Monoid a) => k -> Trie k a -> a
lookup k t = root (path (flatten k) t)

extend :: (Flat k, Monoid a) => Base k -> Trie k a -> Trie k a
extend k (Single x) = Trie (listArray (maxRange k) (repeat nil)) x
extend _ t = t

insert' :: (Flat k, Monoid a) => [Base k] -> a -> Trie k a -> Trie k a
insert' [] v (Single v') = Single (v `mappend` v')
insert' [] v (Trie a v') = Trie a (v `mappend` v')
insert' (k:ks) v t = Trie (modify (insert' ks v) k a) vs
    where Trie a vs = extend k t
          modify f k a = a // [(k, f (a ! k))]

insert :: (Flat k, Monoid a) => k -> a -> Trie k a -> Trie k a
insert k v t = insert' (flatten k) v t