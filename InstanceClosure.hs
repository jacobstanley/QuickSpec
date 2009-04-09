module InstanceClosure(IC, runIC, equations, (=?=), (=:=)) where

import Debug.Trace
import Control.Monad.State
import Control.Monad.Writer
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Data.Map(Map)
import qualified Data.Map as Map
import CongruenceClosure(CC)
import qualified CongruenceClosure as CC
import UnionFind(UF)
import qualified UnionFind as UF
import Term

data S = S {
      eqs :: [(Term, Term)],
      flat :: Map [Maybe Symbol] Int,
      substs :: Term -> Term -> [Term] -> [(Term, Term)]
    }

instance Show S where
    show s = "{ eqs = " ++ show (eqs s) ++ ", meaning = " ++ "" ++ " }"

modifyEqs f = modify (\s -> s { eqs = f (eqs s)})
modifyFlat f = modify (\s -> s { flat = f (flat s)})

register t n = modifyFlat (Map.insertWith (\x y -> y) (flattenTerm t) n)

type IC = WriterT [(Term, Term)] (StateT S (CC Term))

runIC :: (Term -> Term -> [Term] -> [(Term, Term)]) -> [Symbol] -> IC a -> (a, [(Term, Term)])
runIC substs ctx m = CC.runCC App min (map Sym ctx) (evalStateT (runWriterT (init >> m)) (S [] Map.empty substs))
    where init = mapM_ (\s -> register (Sym s) (label s)) ctx

equations :: IC [(Term, Term)]
equations = fmap eqs get

(=:=) :: Term -> Term -> IC ()
t =:= u = do
      r <- t =?= u
      when (not r) $ do
            tell [(t, u)]
            modifyEqs ((t, u):)
            addInstances

liftCC :: CC Term a -> IC a
liftCC = lift . lift

addInstances :: IC ()
addInstances = do
  s <- get
  (before, rs) <- fmap (unzip . IntMap.toList) (liftCC CC.reps)
  let allEqs = [substs s t u rs | (t, u) <- eqs s]
  forM_ (concat allEqs) $ \(t, u) -> do
    s1 <- flatten t
    s2 <- flatten u
    {- trace (show (s1, s2, t, u)) $ -}
    liftCC (s1 CC.=:= s2)
  after <- fmap (map fst . IntMap.toList) (liftCC CC.reps)
  when (before /= after) addInstances

(=?=) :: Term -> Term -> IC Bool
t@(App f x) =?= u@(App g y) = orM [andM [f =?= g, x =?= y], t `cceq` u]
t =?= u = t `cceq` u
t `cceq` u = frozen $ do
  s1 <- flatten t
  s2 <- flatten u
  r1 <- liftCC (CC.rep s1)
  r2 <- liftCC (CC.rep s2)
  return (r1 == r2)

orM [] = return False
orM (x:xs) = do
  b <- x
  if b then return True else orM xs
andM [] = return True
andM (x:xs) = do
  b <- x
  if b then andM xs else return False

flatten :: Term -> IC Int
flatten t = do
  r <- fmap (Map.lookup (flattenTerm t) . flat) get
  case r of
    Just n -> return n
    Nothing -> flatten' t
flatten' (Sym s) = return (label s)
flatten' s@(App t u) = do
  s1 <- flatten t
  s2 <- flatten u
  r <- liftCC (s1 CC.$$ s2)
  register s r
  return r

frozen :: IC a -> IC a
frozen m = do
  s1 <- get
  s2 <- liftCC get
  s3 <- liftCC (lift get)
  r <- m
  put s1
  liftCC (put s2)
  liftCC (lift (put s3))
  return r
