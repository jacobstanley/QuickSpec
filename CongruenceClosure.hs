-- Based on the paper "Proof-producing Congruence Closure".

module CongruenceClosure(CC, newSym, (=:=), (=?=), rep, reps, runCC, ($$), S, frozen) where

import Prelude hiding (lookup)
import Control.Monad.State.Strict
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import UnionFind(UF, Replacement((:>)))
import qualified UnionFind as UF
import Data.Maybe
import Data.List(foldl')

lookup2 :: Int -> Int -> IntMap (IntMap a) -> Maybe a
lookup2 k1 k2 m = IntMap.lookup k2 (IntMap.findWithDefault IntMap.empty k1 m)

insert2 :: Int -> Int -> a -> IntMap (IntMap a) -> IntMap (IntMap a)
insert2 k1 k2 v m = IntMap.insertWith IntMap.union k1 (IntMap.singleton k2 v) m

delete2 :: Int -> Int -> IntMap (IntMap a) -> IntMap (IntMap a)
delete2 k1 k2 m = IntMap.adjust (IntMap.delete k2) k1 m

data FlatEqn = (Int, Int) := Int deriving (Eq, Ord)

data S a = S {
      funUse :: !(IntMap [(Int, Int)]),
      argUse :: !(IntMap [(Int, Int)]),
      lookup :: IntMap (IntMap Int),
      app :: a -> a -> a
    }

type CC a = StateT (S a) (UF a)

modifyFunUse f = modify (\s -> s { funUse = f (funUse s) })
modifyArgUse f = modify (\s -> s { argUse = f (argUse s) })
addFunUses xs s = modifyFunUse (IntMap.insertWith (++) s xs)
addArgUses xs s = modifyArgUse (IntMap.insertWith (++) s xs)
modifyLookup f = modify (\s -> s { lookup = f (lookup s) })
putLookup l = modifyLookup (const l)

newSym :: a -> CC a Int
newSym x = lift (UF.newSym x)

($$) :: Int -> Int -> CC a Int
f $$ x = do
  m <- gets lookup
  a <- gets app
  (f', fv) <- rep f
  (x', xv) <- rep x
  case lookup2 x' f' m of
    Nothing -> do
      c <- newSym (fv `a` xv)
      putLookup (insert2 x' f' c m)
      addFunUses [(x', c)] f'
      addArgUses [(f', c)] x'
      return c
    Just k -> return k

(=:=) :: Int -> Int -> CC a Bool
a =:= b = propagate (a, b)

t =?= u = do
  (r1, _) <- rep t
  (r2, _) <- rep u
  return (r1 == r2)

propagate (a, b) = do
  (unified, pending) <- propagate1 (a, b)
  mapM_ propagate pending
  return unified

propagate1 (a, b) = do
  res <- lift (a UF.=:= b)
  case res of
    Nothing -> return (False, [])
    Just (r :> r') -> do
      funUses <- gets (IntMap.lookup r . funUse)
      argUses <- gets (IntMap.lookup r . argUse)
      case (funUses, argUses) of
        (Nothing, Nothing) -> return (True, [])
        _ -> fmap (\x -> (True, x)) (updateUses r r' (fromMaybe [] funUses) (fromMaybe [] argUses))

updateUses r r' funUses argUses = do
  modifyFunUse (IntMap.delete r)
  modifyArgUse (IntMap.delete r)
  modifyLookup (IntMap.delete r)
  forM_ funUses $ \(x, c) -> modifyLookup (delete2 x r)
  let repPair (x, c) = do
        (x', _) <- rep x
        return (x', c)
  funUses' <- mapM repPair funUses
  argUses' <- mapM repPair argUses

  m <- gets lookup

  let foldUses insert lookup pending m uses = foldl' op e uses
        where op (pending, newUses, m) (x', c) =
                case lookup x' m of
                  Just k -> ((c, k):pending, newUses, m)
                  Nothing -> (pending, (x', c):newUses, insert x' c m)
              e = (pending, [], m)

      (funPending, funNewUses, m') = foldUses (\x' c m -> insert2 x' r' c m)
                                              (\x' m -> lookup2 x' r' m)
                                              [] m funUses'

      (pending, argNewUses, argM) = foldUses IntMap.insert IntMap.lookup funPending
                                             (IntMap.findWithDefault IntMap.empty r' m')
                                             argUses'

  addFunUses funNewUses r'
  addArgUses argNewUses r'

  putLookup (if IntMap.null argM then m' else IntMap.insert r' argM m')

  return pending

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
runCC app min syms m = UF.runUF min syms (evalStateT m (S IntMap.empty IntMap.empty IntMap.empty app))
