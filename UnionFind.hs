module UnionFind(UF, Replacement((:>)), newSym, (=:=), rep, reps, runUF, S) where

import Prelude hiding (min)
import Text.Show.Functions
import Control.Monad.State.Strict
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap

data S a = S {
      links :: IntMap Int,
      repSet :: IntMap a,
      sym :: Int,
      min :: a -> a -> a
    } deriving Show

type UF a = State (S a)
data Replacement = Int :> Int

runUF :: (s -> s -> s) -> [s] -> UF s a -> a
runUF min syms m = fst (runState (zipWithM_ insertRep [0..] syms >> m) (S IntMap.empty IntMap.empty (length syms) min))

modifyLinks f = modify (\s -> s { links = f (links s) })
modifyReps f = modify (\s -> s { repSet = f (repSet s) })
modifySym f = modify (\s -> s { sym = f (sym s) })
putLinks l = modifyLinks (const l)

newSym :: a -> UF a Int
newSym v = do
  s <- get
  insertRep (sym s) v
  modifySym (+1)
  return (sym s)

insertRep s v = modifyReps (IntMap.insert s v)

(=:=) :: Int -> Int -> UF s (Maybe Replacement)
s =:= t = do
  (rs, vs) <- rep s
  (rt, vt) <- rep t
  if (rs /= rt) then do
    min_ <- fmap min get
    modifyLinks (IntMap.insert rs rt)
    modifyReps (IntMap.delete rs)
    modifyReps (IntMap.insert rt (vs `min_` vt))
    return (Just (rs :> rt))
   else return Nothing

s =?= t = liftM2 (==) (rep s) (rep t)

rep :: Int -> UF s (Int, s)
rep t = do
  m <- fmap links get
  case IntMap.lookup t m of
    Nothing -> fmap (\s -> (t, IntMap.findWithDefault undefined t (repSet s))) get
    Just t' -> do
      (r, v) <- rep t'
      putLinks (IntMap.insert t r m)
      return (r, v)

reps :: UF s (IntMap s)
reps = fmap repSet get
