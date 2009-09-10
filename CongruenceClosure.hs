-- Based on the paper "Proof-producing Congruence Closure".

module CongruenceClosure(CC, newSym, (=:=), (=?=), rep, reps, runCC, ($$), S, frozen) where

import Prelude hiding (lookup)
import Control.Monad.State.Strict
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Data.Set(Set)
import qualified Data.Set as Set
import UnionFind(UF, Replacement((:>)))
import qualified UnionFind as UF

lookup2 :: Int -> Int -> IntMap (IntMap a) -> Maybe a
lookup2 k1 k2 m = IntMap.lookup k2 (IntMap.findWithDefault IntMap.empty k1 m)

insert2 :: Int -> Int -> a -> IntMap (IntMap a) -> IntMap (IntMap a)
insert2 k1 k2 v m = IntMap.insertWith IntMap.union k1 (IntMap.singleton k2 v) m

data FlatEqn = (Int, Int) := Int deriving (Eq, Ord, Show)

data S a = S {
      use :: IntMap (Set FlatEqn),
      lookup :: IntMap (IntMap FlatEqn),
      app :: a -> a -> a
    } deriving Show

type CC a = StateT (S a) (UF a)

modifyUse f = modify (\s -> s { use = f (use s) })
modifyLookup f = modify (\s -> s { lookup = f (lookup s) })
putLookup l = modifyLookup (const l)

newSym :: a -> CC a Int
newSym x = do
  s <- lift (UF.newSym x)
  insertSym s
  return s

insertSym :: Int -> CC a ()
insertSym s = modifyUse (IntMap.insert s Set.empty)

($$) :: Int -> Int -> CC a Int
f $$ x = do
  m <- fmap lookup get
  a <- fmap app get
  (f', fv) <- rep f
  (x', xv) <- rep x
  case lookup2 f' x' m of
    Nothing -> do
      c <- newSym (fv `a` xv)
      putLookup (insert2 f' x' ((f, x) := c) m)
      mapM_ (addUse ((f, x) := c)) [f', x']
      return c
    Just ((g, y) := k) -> return k

(=:=) :: Int -> Int -> CC a Bool
a =:= b = propagate (a, b)

t =?= u = do
  (r1, _) <- rep t
  (r2, _) <- rep u
  return (r1 == r2)

propagate (a, b) = do
  (unified, pending) <- propagate1 (a, b)
  mapM_ propagate (concat pending)
  return unified

propagate1 (a, b) = do
  res <- lift (a UF.=:= b)
  case res of
    Nothing -> return (False, [])
    Just (r :> r') -> fmap (\x -> (True, x)) $ do
      u <- fmap use get
      forM (Set.toList (IntMap.findWithDefault undefined r u)) $ \((f, x) := c) -> do
        removeUse ((f, x) := c) r
        (f', _) <- rep f
        (x', _) <- rep x
        m <- fmap lookup get
        case lookup2 f' x' m of
          Just ((g, y) := k) -> return [(c, k)]
          Nothing -> do
            modifyLookup (insert2 f' x' ((f, x) := c))
            addUse ((f, x) := c) r'
            return []

addUse e s = modifyUse (IntMap.update (Just . (Set.insert e)) s)
removeUse e s = modifyUse (IntMap.update (Just . (Set.delete e)) s)

rep :: Int -> CC a (Int, a)
rep s = lift (UF.rep s)
reps :: CC a (IntMap a)
reps = lift UF.reps

frozen :: CC s a -> CC s a
frozen x = do
  s <- get
  s' <- lift get
  r <- x
  put s
  lift (put s')
  return r

runCC :: (s -> s -> s) -> (s -> s -> s) -> [s] -> CC s a -> a
runCC app min syms m = UF.runUF min syms (evalStateT (mapM_ insertSym [0..length syms-1] >> m) (S IntMap.empty IntMap.empty app))
