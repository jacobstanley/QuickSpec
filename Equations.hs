{-# LANGUAGE GADTs,ScopedTypeVariables #-}
module Equations where

import Control.Arrow
import Control.Monad.Writer
import Control.Parallel.Strategies
import Data.Array hiding (range)
import Data.List
import Data.Ord
import Data.Typeable
import qualified Data.Map as Map
import System.IO
import System.Random
import Text.Printf
import Term hiding (evaluate)
import CongruenceClosure

-- Term generation.

type Context = [Symbol]
type Universe = TypeRep -> [Term Symbol]

terms :: Context -> Universe -> Universe
terms ctx base ty =
     [ sym elt
     | elt <- ctx
     , symbolType elt == ty
     , let sym = case typ elt of
                   TVar -> Var
                   TConst -> Const
     ]
  ++ [ App f x
     | ty' <- argTypes ctx ty
     , x  <- base ty'
     , not (termIsUndefined x)
     , f  <- terms ctx base (mkFunTy ty' ty)
     , not (termIsUndefined f)
     ]

argTypes ctx ty = [ ty1 | (ty1, ty2) <- funTypes (allTypes ctx),
                          ty2 == ty ]
termIsUndefined (Const s) = isUndefined s
termIsUndefined _ = False

terms' :: Context -> Universe -> Universe
terms' ctx base ty = nubSort
     (terms ctx base ty ++
       [ App (Const f) x
       | ty' <- argTypes ctx ty
       , f <- ctx
       , symbolType f == mkFunTy ty' ty
       , x <- terms ctx base ty' ])

nubSort :: Ord a => [a] -> [a]
nubSort = map head . partitionBy id

undefinedSyms :: Context -> Context
undefinedSyms = typeNub . concatMap (makeUndefined . symbolClass) . typeNub
  where typeNub = nubBy (\s1 s2 -> symbolType s1 == symbolType s2)
        makeUndefined (Data x) =
          Symbol { name = "undefined", label = undefined, description = Nothing,
                   isUndefined = True, typ = TConst, range = return (Data (undefined `asTypeOf` x)) }:
          case funTypes [typeOf x] of
            [] -> []
            _ -> makeUndefined (rhs x)

-- Equivalence class refinement.

data Condition = Always | Symbol :/= Symbol deriving (Eq, Ord, Show)
satisfied :: Ord a => (Symbol -> a) -> Condition -> Bool
satisfied value (a :/= b) = value a /= value b
satisfied value Always = True

data Classes a = Classes [Condition -> Bool] [TestResults a]
data TestResults a = TestResults [a] [[Int]]

pack :: [[a]] -> Classes a
pack xss = Classes [] [ TestResults xs [] | xs <- xss ]

evaluate :: Ord b => [(a -> b, Condition -> Bool)] -> Classes a -> Classes a
evaluate ss (Classes cs rss) = Classes (cs ++ map snd ss)
                                       [ TestResults xs (vss ++ map (evaluate1 xs) ss)
                                       | TestResults xs vss <- rss ]
  where evaluate1 xs (eval, _) = collate (map eval xs)
        collate vs = [ Map.findWithDefault undefined v m | v <- vs ] `using` seqList rwhnf
          where m = Map.fromList (zip (nubSort vs) [0..])

restrict :: Condition -> Classes a -> Classes a
restrict c (Classes ps rss) = Classes (filter keep ps) (map restrict1 rss)
  where keep p = p c
        restrict1 (TestResults xs vss) =
          TestResults xs [ vs | (p, vs) <- zip ps vss, p c ]

limit :: Int -> Classes a -> Classes a
limit n (Classes ps rss) = Classes (take n ps) (map limit1 rss)
  where limit1 (TestResults xs rss) = TestResults xs (take n rss)

unpack :: Classes a -> [[a]]
unpack (Classes _ rss) = concatMap unpack1 rss
  where unpack1 (TestResults xs vss) = map (map fst) (partitionBy snd (zip xs (transpose vss)))

parRefine :: ([a] -> [[a]]) -> ([[a]] -> [[a]])
parRefine f xs = parFlatMap (parList r0) f xs
--parRefine = concatMap

partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
partitionBy value = map (map fst) . groupBy (\x y -> snd x == snd y) . sortBy (comparing snd) . map (id &&& value)

-- Pruning.

-- A single unary function doesn't increase depth, but two in a row
-- do.
varDepths d (App (Const s) t) = varDepths1 d t
varDepths d t = varDepths1 d t

varDepths1 d (App s t) = varDepths1 d s `merge` varDepths (d-1) t
varDepths1 d (Var x)   = [(x,d)]
varDepths1 d _         = []

[]          `merge` yks = yks
xks         `merge` []  = xks
((x,k):xks) `merge` ((y,n):yns)
  | x < y     = (x,k) : (xks `merge` ((y,n):yns))
  | x == y    = (x, k `min` n) : (xks `merge` yns)
  | otherwise = (y,n) : (((x,k):xks) `merge` yns)

consequences :: Int -> [(Int, Int, TypeRep)] -> [Symbol] -> (Term Int, Term Int) -> CC ()
consequences d univ rigid (t, u) = mapM_ unify (cons1 t u `mplus` cons1 u t)
    where unify (x, y) = do
            x' <- flatten x
            y' <- flatten y
            x' =:= y'
          cons1 t u = do
            s <- mapM substs [ (v,d) | (v, d) <- varDepths d t, v `notElem` rigid ]
            s' <- case rigid of
                    [] -> [[]]
                    [i, j] -> [[(i, Const (label j)), (j, Const (label i))], []]
            return (subst (s ++ s') t, subst (s ++ s') u)
          substs (v, d) = [ (v, Const s) | (_, s, ty) <- takeWhile (\(d', _, _) -> d' <= d) univ, ty == symbolType v ]

flatten (Var s) = return (label s)
flatten (Const s) = return s
flatten (App t u) = do
  t' <- flatten t
  u' <- flatten u
  t' $$ u'

killSymbols (Var s) = Var s
killSymbols (Const s) = Const (label s)
killSymbols (App t u) = App (killSymbols t) (killSymbols u)

prune1 :: Int -> [(Int, Int, TypeRep)] -> [Symbol] -> [(Term Symbol, Term Symbol)] -> CC [(Term Symbol, Term Symbol)]
prune1 d univ rigid es = fmap snd (runWriterT (mapM_ (consider univ) es))
    where consider univ (t, u) = do
            b <- lift (canDerive t u)
            when (not b) $ do
              tell [(t, u)]
              lift (consequences d univ rigid (killSymbols t, killSymbols u))
{-
prune2 :: Int -> [(Int, Int, TypeRep)] -> [(Term Symbol, Term Symbol)] -> [(Term Symbol, Term Symbol)] -> CC () [(Term Symbol, Term Symbol)]
prune2 d univ committed [] = return committed
prune2 d univ committed ((t,u):es) = do
  b <- frozen $ do
         forM_ (committed ++ es) $ \(t, u) -> consequences d univ (killSymbols t, killSymbols u)
         canDerive t u
  if b then prune2 d univ committed es
       else prune2 d univ ((t,u):committed) es
-}
loadUniv :: [Term Symbol] -> CC [(Int, Int, TypeRep)]
loadUniv univ = fmap (sortBy (comparing (\(d,_,_) -> d))) (mapM f univ)
    where f t = do
            t' <- flatten (killSymbols t)
            return (depth t, t', termType t)

prune :: Context -> Int -> [Term Symbol] -> [(Term Symbol, Term Symbol)] -> [(Condition, [(Term Symbol, Term Symbol)])] -> [(Condition, Term Symbol, Term Symbol)]
prune ctx d univ0 es ess = runCCctx ctx $ do
  univ <- loadUniv univ0
  es' <- fmap (map (\(t, u) -> (Always, t, u))) (prune1 d univ [] es)
  ess' <- mapM (\(cond, es) -> fmap (map (\(t, u) -> (cond, t, u))) (frozen (prune1 d univ (condVars cond) es))) ess
  return (es' ++ concat ess')

condVars (a :/= b) = [a, b]
condVars Always = []

runCCctx :: Context -> CC a -> a
runCCctx ctx x = runCC (length ctx) x

canDerive :: Term Symbol -> Term Symbol -> CC Bool
canDerive t u = do
  t' <- flatten (killSymbols t)
  u' <- flatten (killSymbols u)
  t' =?= u'

subst :: [(Symbol, Term a)] -> Term a -> Term a
subst sub (App s t) = App (subst sub s) (subst sub t)
subst sub t@(Var s) = head ([ t | (v,t) <- sub, s == v ] ++ [ t ])
subst sub s         = s

-- Main program.

genSeeds :: IO [(StdGen, Int)]
genSeeds = do
  rnd <- newStdGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..20])))

-- A definition is something of the form
--   f x1..xn = u
-- where all the xi are distinct variables, there is at least one
-- parameter to f, and if there is an application of f inside u,
-- then one of the xi mustn't appear in that application.
isDefinition (u, t) = typ (fun t) == TConst && all isVar (args t) && not (null (args t)) && nub (args t) == args t && acyclic u
  where isVar (Var _) = True
        isVar _ = False
        isCon (Const _) = True
        isCon _ = False
        acyclic u = all acyclic (args u) && acyclicTop u
        acyclicTop u
          | fun t == fun u = nub (map Var (vars u)) `isProperSubsetOf` args t
          | otherwise = True
        xs `isProperSubsetOf` ys = sort xs `isSublistOf` sort ys && sort xs /= sort ys
        [] `isSublistOf` _ = True
        (x:xs) `isSublistOf` [] = False
        (x:xs) `isSublistOf` (y:ys) | x == y = xs `isSublistOf` ys
                                    | otherwise = (x:xs) `isSublistOf` ys

definitions es = nubBy (\(_, t) (_, t') -> fun t == fun t') (filter isDefinition es)

allOfThem = const True
about xs = any (\s -> description s `elem` map Just xs) . symbols

laws depth ctx0 p = do
  hSetBuffering stdout NoBuffering
  let ctx = zipWith relabel [0..] (ctx0 ++ undefinedSyms ctx0)
  putStrLn "== API =="
  putStrLn "-- functions"
  sequence_ [ putStrLn (show (Const elt) ++ " :: " ++ show (symbolType elt))
            | elt <- ctx
            , typ elt == TConst && not (isUndefined elt)
            ]
  putStrLn "-- variables"
  sequence_ [ putStrLn (name elt ++ " :: " ++ show (symbolType elt))
            | elt <- ctx
            , typ elt == TVar && not (isUndefined elt)
            ]
  seeds <- genSeeds
  putStrLn "== classes =="
  cs <- tests depth ctx seeds
  let eqs cond = map head
               $ partitionBy equationOrder
               $ [ (y,x) | x:xs <- map sort (unpack (restrict cond cs)), funTypes [termType x] == [], y <- xs ]
  printf "%d raw equations.\n\n" (length (eqs Always))
  let univ = concat (unpack cs)
  printf "Universe has %d terms.\n" (length univ)
  putStrLn "== definitions =="
  sequence_
       [ putStrLn (show i ++ ": "++ show x ++ " := " ++ show y)
       | (i, (y,x)) <- zip [1..] (definitions (eqs Always))
       ]
  putStrLn "== equations =="
  let interesting (_, x, y) = p x || p y
      conds = [ i :/= j | (i:j:_) <- partitionBy (show . symbolType) (filter (\s -> typ s == TVar) ctx) ]
      pruned = filter interesting (prune ctx depth univ (eqs Always) [ (cond, eqs cond) | cond <- conds ])
  sequence_
       [ putStrLn (show i ++ ": " ++ concat [ show x ++ "/=" ++ show y ++ " => " | x :/= y <- [cond] ] ++ show y ++ " == " ++ show x)
       | (i, (cond, y,x)) <- zip [1..] pruned
       ]
  forM_ pruned $ \(cond, y, x) -> do
    let c = head (filter (\(x':_) -> x == x') (map sort (unpack cs)))
        commonVars = foldr1 intersect (map vars c)
        subsumes t = sort (vars t) == sort commonVars
    when (cond == Always && not (any subsumes c)) $
         printf "*** missing term: %s = ???\n"
                (show (mapVars (\s -> if s `elem` commonVars then s else s { name = "_" ++ name s }) x))

test :: Int -> Context -> [(StdGen, Int)] -> (TypeRep -> [Term Symbol]) -> IO (Classes (Term Symbol))
test depth ctx seeds base = do
  printf "Depth %d: " depth
  let cs0 = filter (not . null) [ terms ctx base ty | ty <- allTypes ctx ]
  printf "%d terms, " (length (concat cs0))
  let evals = [ toValue . eval (memoSym ctx ctxFun) | (ctxFun, toValue) <- map useSeed seeds ]
      conds = map (\f -> satisfied (f . Const)) evals
      cs1 = evaluate (take 100 (zip evals conds)) (pack cs0)
  printf "%d classes, %d raw equations.\n"
         (length (unpack cs1))
         (sum (map (subtract 1 . length) (unpack cs1)))
  return cs1

memoSym :: Context -> (Symbol -> a) -> (Symbol -> a)
memoSym ctx f = (arr !) . label
  where arr = listArray (0, length ctx - 1) (map f ctx)

-- tests :: Int -> Context -> [(StdGen, Int)] -> Int -> IO (Int, Classes (Term Symbol))
-- tests 0 _ _ _ = return (0, Classes [] [] [])
-- tests (d+1) ctx vals start = do
--   (n0, cs0) <- tests d ctx vals start
--   let reps = map head (snd (refine start 50 (extract cs0)))
--       base ty = [ t | t <- reps, termType t == ty ]
--   (n, cs) <- test (d+1) ctx vals start base
--   (_, cs1) <- tests d ctx vals n
--   return (n, cs)
-- --  if cs0 == cs1 then return (n, cs) else tests (d+1) ctx vals n

tests :: Int -> Context -> [(StdGen, Int)] -> IO (Classes (Term Symbol))
tests 0 _ _ = return (pack [])
tests d ctx vals = do
  cs0 <- tests (d-1) ctx vals
  let reps = map head (map sort (unpack cs0))
      base ty = [ t | t <- reps, termType t == ty ]
  test d ctx vals base
