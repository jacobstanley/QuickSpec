module TermCongruenceClosure(TCC, runTCC, (=?=), (=:=)) where

import Control.Monad.State
import Control.Monad.Writer
import Data.Map(Map)
import qualified Data.Map as Map
import CongruenceClosure(CC)
import qualified CongruenceClosure as CC
import Term

type S = Map [Maybe Symbol] Int
type TCC = StateT S (CC Term)

register :: Term -> Int -> TCC ()
register t n = modify (Map.insertWith (\x y -> y) (flattenTerm t) n)

runTCC :: [Symbol] -> TCC a -> a
runTCC ctx m = CC.runCC App min (map Sym ctx) (evalStateT (init >> m) Map.empty)
    where init = mapM_ (\s -> register (Sym s) (label s)) ctx

(=:=) :: Term -> Term -> TCC Bool
t =:= u = do
  s1 <- flatten t
  s2 <- flatten u
  lift (s1 CC.=:= s2)

(=?=) :: Term -> Term -> TCC Bool
t@(App f x) =?= u@(App g y) = orM [andM [f =?= g, x =?= y], t `cceq` u]
t =?= u = t `cceq` u
t `cceq` u = frozen $ do
  s1 <- flatten t
  s2 <- flatten u
  (r1, _) <- lift (CC.rep s1)
  (r2, _) <- lift (CC.rep s2)
  return (r1 == r2)

orM [] = return False
orM (x:xs) = do
  b <- x
  if b then return True else orM xs
andM [] = return True
andM (x:xs) = do
  b <- x
  if b then andM xs else return False

flatten :: Term -> TCC Int
flatten t = do
  r <- fmap (Map.lookup (flattenTerm t)) get
  case r of
    Just n -> return n
    Nothing -> flatten' t
flatten' (Sym s) = return (label s)
flatten' s@(App t u) = do
  s1 <- flatten t
  s2 <- flatten u
  r <- lift (s1 CC.$$ s2)
  register s r
  return r

frozen :: TCC a -> TCC a
frozen m = do
  s1 <- get
  s2 <- lift get
  s3 <- lift (lift get)
  r <- m
  put s1
  lift (put s2)
  lift (lift (put s3))
  return r
