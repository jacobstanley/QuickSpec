{-# LANGUAGE TypeFamilies, FlexibleContexts, TupleSections #-}
module Subst where

import Family
import UntypedTerm
import TestTree
import Utils
import Control.Monad
import Data.List
import qualified Data.Map as Map
import Data.Map(Map)
import CongruenceClosure
import qualified CongruenceClosure as CC
import Control.Monad.Writer
import Control.Exception
import Data.Ord

-- Perhaps we don't need the Term stuff explicitly at all---rather,
-- have a typeclass with all the CC operations:
-- class BuildTerm a where
--   app :: a -> a -> a
--   const :: String -> a
--   var :: ...
-- and have an instance BuildTerm CC, giving laws a type signature
-- laws :: (forall b. BuildTerm b => a -> b) -> TestResults a -> IO ().
--
-- Need to think about what "var" should look like in that case.

type TermFor a = Term (Symbol (WithBound (Bound a) a))

-- To do: GET RID of the Term type entirely. It causes major headaches
-- when it comes to sorting the equations.
class Ord (Bound a) => TermLike a where
  type Bound a
  term :: a -> TermFor a

data Symbol a = Var String a | ConstS String
  deriving (Eq, Ord)

name :: Symbol a -> String
name (Var x _) = x
name (ConstS x) = x

instance Show (Symbol a) where
  show (ConstS x) = x
  show (Var x _) = x

laws :: TermLike a => TestResults a -> IO ()
laws rs = do
  let cs = sort (map sort (map (map term) (classes rs)))
      families = fmap (map term) $ Map.fromList
        [ (Family.bound f, Family.terms f)
        | ts <- cs,
          t <- ts,
          f <- vars t ]
  
      names = usort [ x | ts <- cs, t <- ts, x <- namesOf t ]
      namesMap = Map.fromList (zip names [0..])
      vars App { fun = f, revArgs = as } =
        [ x | Var _ x <- [f] ] ++ concatMap vars as
      namesOf App { fun = f, revArgs = as } = name f:concatMap namesOf as

      s = initial (length names)

      eqs = evalCC (initial (length names)) . execWriterT $ prune cs families namesMap

  forM_ eqs $ \(x, y) -> do
    putStr (show x)
    putStr " = "
    putStrLn (show y)

prune :: TermLike a => [[TermFor a]] -> Map (Bound a) [TermFor a] -> Map String Int -> WriterT [(TermFor a, TermFor a)] CC ()
prune cs families names = do
  cs' <- fmap (zipWith zip cs) $ mapM (mapM (lift . flattenTerm names)) cs
  let flattenFamily names (k, v) = fmap (k,) (mapM (flattenTerm names) v)
  families' <- fmap Map.fromList (mapM (lift . flattenFamily names) (Map.toList families))
  let eqs0 = sortBy (comparing stuff) [ (u, t) | (t:ts) <- cs', u <- ts ]
      stuff ((u,_), (t,_)) = (containsP u || containsP t, size t `max` size u, -length (nub (freeVars u ++ freeVars t)), u, t)
      containsP App { fun = f, revArgs = as } = take 1 (name f) == "p" || any containsP as
      size App { revArgs = as } = 1 + sum (map size as)
      freeVars App { fun = f@(Var _ _), revArgs = as } = name f:concatMap freeVars as
      freeVars App { revArgs = as } = concatMap freeVars as
  pruneLoop families' names eqs0

pruneLoop :: TermLike a => Map (Bound a) [Int] ->
             Map String Int -> 
             [((TermFor a, Int), (TermFor a, Int))] ->
             WriterT [(TermFor a, TermFor a)] CC ()
pruneLoop _ _ [] = return ()
pruneLoop families names (((t, m), (u, n)):eqs) = do
  b <- lift (m =?= n)
  unless b $ do
    tell [(t, u)]
    forM_ (substs families t ++ substs families u) $ \s -> do
      let names' = Map.fromList s `Map.union` names
      t' <- lift (flattenTerm names' t)
      u' <- lift (flattenTerm names' u)
      lift (t' =:= u')
  pruneLoop families names eqs

substs :: TermLike a => Map (Bound a) [Int] -> TermFor a -> [[(String, Int)]]
substs families t = mapM (\(x, y) -> map (x,) (Map.findWithDefault (error "substs: missing family") y families))
                      (bounds t)
  where bounds App { fun = f, revArgs = as } = foldr1 (merge same fst) (funBounds f:map bounds as)
        funBounds (Var x b) = [(x, bound b)]
        funBounds (ConstS _) = []
        same (x, b1) (y, b2) = assert (x == y) $ (x, b1 `min` b2)

flattenTerm :: Map String Int -> Term (Symbol a) -> CC Int
flattenTerm names t = do
  args' <- mapM (flattenTerm names) (args t)
  foldM ($$)
          (Map.findWithDefault (error "flattenTerm: missing name")
                (name (fun t)) names)
          args'
