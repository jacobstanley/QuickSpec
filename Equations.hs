{-# LANGUAGE GADTs,ScopedTypeVariables #-}
module Equations where

import Control.Arrow
import Control.Monad.Writer
import Control.Parallel.Strategies
import Data.Array hiding (range)
import Data.List
import Data.Ord
import Data.Typeable
import System.IO
import System.Random
import Text.Printf
import Term
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
  where nubSort = map head . partitionBy compare

undefinedSyms :: Context -> Context
undefinedSyms = typeNub . concatMap (makeUndefined . symbolClass) . typeNub
  where typeNub = nubBy (\s1 s2 -> symbolType s1 == symbolType s2)
        makeUndefined (Data x) =
          Symbol { name = "undefined", label = undefined, isUndefined = True, typ = TConst,
                   range = return (Data (undefined `asTypeOf` x)) }:
          case funTypes [typeOf x] of
            [] -> []
            _ -> makeUndefined (rhs x)

-- Equivalence class refinement.

iterateUntil :: Eq b => Int -> (a -> b) -> (a -> a) -> a -> (Int, a)
iterateUntil start p f x = extract (head (filter eq (drop start (zip3 xs (tail xs) [0..]))))
    where xs = iterate f x
          eq (a, b, _) = p a == p b
          extract (x, _, n) = (n, x)

refine :: Ord b => Int -> Int -> ([a] -> Bool) -> (a -> [b]) -> [[a]] -> (Int, [[a]])
refine start step trivial eval xss = flatten (iterateUntil start length (refine1 step) (map (map (\x -> (x, eval x))) xss))
    where flatten (n, xss) = (n, map (map fst) xss)
          refine1 0 = id
          refine1 step = parRefine (refine1 (step-1) . split)
          first (x, (v:vs)) = v
          next (x, (v:vs)) = (x, vs)
          split = map (map next) . filter (not . trivial . map fst) . partitionBy (comparing first)

parRefine :: ([a] -> [[a]]) -> ([[a]] -> [[a]])
parRefine f = parFlatMap (parList (parList r0)) f

partitionBy :: (a -> a -> Ordering) -> [a] -> [[a]]
partitionBy compare = groupBy (\x y -> x `compare` y == EQ) . sortBy compare

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

consequences :: Int -> [(Int, Int, TypeRep)] -> (Term Int, Term Int) -> CC () ()
consequences d univ (t, u) = mapM_ unify (cons1 t u `mplus` cons1 u t)
    where unify (x, y) = do
            x' <- flatten x
            y' <- flatten y
            x' =:= y'
          cons1 t u = do
            s <- mapM substs [ (v, d' `min` (d-1)) | (v, d') <- varDepths d t ]
            return (subst s t, subst s u)
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

prune1 :: Int -> [(Int, Int, TypeRep)] -> [(Term Symbol, Term Symbol)] -> CC () [(Term Symbol, Term Symbol)]
prune1 d univ es = fmap snd (runWriterT (mapM_ (consider univ) es))
    where consider univ (t, u) = do
            b <- lift (canDerive t u)
            when (not b) $ do
              tell [(t, u)]
              lift (consequences d univ (killSymbols t, killSymbols u))

prune2 :: Int -> [(Int, Int, TypeRep)] -> [(Term Symbol, Term Symbol)] -> [(Term Symbol, Term Symbol)] -> CC () [(Term Symbol, Term Symbol)]
prune2 d univ committed [] = return committed
prune2 d univ committed ((t,u):es) = do
  b <- frozen $ do
         forM_ (committed ++ es) $ \(t, u) -> consequences d univ (killSymbols t, killSymbols u)
         canDerive t u
  if b then prune2 d univ committed es
       else prune2 d univ ((t,u):committed) es

loadUniv :: [Term Symbol] -> CC a [(Int, Int, TypeRep)]
loadUniv univ = fmap (sortBy (comparing (\(d,_,_) -> d))) (mapM f univ)
    where f t = do
            t' <- flatten (killSymbols t)
            return (depth t, t', termType t)

prune :: Context -> Int -> [Term Symbol] -> [(Term Symbol, Term Symbol)] -> [(Term Symbol, Term Symbol)]
prune ctx d univ0 es = runCCctx ctx $ do
  univ <- loadUniv univ0
  es' <- frozen (prune1 d univ es)
--  prune2 d univ [] (reverse (sort es'))
  return es'

runCCctx :: Context -> CC () a -> a
runCCctx ctx x = runCC const const (replicate (length ctx) ()) x

canDerive :: Term Symbol -> Term Symbol -> CC () Bool
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

laws ctx0 depth = someLaws ctx0 (allTypes ctx0) depth

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

someLaws ctx0 types depth = do
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
  (_, cs) <- tests depth ctx (\c -> drop 1 c == []) seeds 0
  let eqs = map head
          $ partitionBy (comparing equationOrder)
          $ [ (y,x) | (x:xs) <- cs, funTypes [termType x] == [], y <- xs ]
  printf "%d raw equations.\n\n" (length eqs)
--  let univ = concat [allTerms depth ctx t | t <- allTypes ctx]
  let univ = concat cs
  printf "Universe has %d terms.\n" (length univ)
  putStrLn "== definitions =="
  sequence_
       [ putStrLn (show i ++ ": "++ show x ++ " := " ++ show y)
       | (i, (y,x)) <- zip [1..] (definitions eqs)
       ]
  putStrLn "== equations =="
  let interesting (x, y) = interesting1 x || interesting1 y
      interesting1 t = any (\t -> termType t `elem` types) (subterms t)
      pruned = filter interesting (prune ctx depth univ eqs)
  sequence_
       [ putStrLn (show i ++ ": "++ show y ++ " == " ++ show x)
       | (i, (y,x)) <- zip [1..] pruned
       ]
  forM_ pruned $ \(y, x) -> do
    let c = head (filter (\(x':_) -> x == x') cs)
        commonVars = foldr1 intersect (map vars c)
        subsumes t = sort (vars t) == sort commonVars
    when (not (any subsumes c)) $
         printf "*** missing term: %s = ???\n"
                (show (mapVars (\s -> if s `elem` commonVars then s else s { name = "_" ++ name s }) x))

test :: Int -> Context -> ([Term Symbol] -> Bool) -> [(StdGen, Int)] -> Int -> (TypeRep -> [Term Symbol]) -> IO (Int, [[Term Symbol]])
test depth ctx trivial seeds start base = do
  printf "Depth %d: " depth
  let cs0 = filter (not . null) [ terms ctx base ty | ty <- allTypes ctx ]
  printf "%d terms, " (length (concat cs0))
  let funs = map ((memoSym ctx *** id) . useSeed) seeds
      evals x = [ toValue (eval ctxFun x) | (ctxFun, toValue) <- funs ]
      (n, cs1) = refine start 50 trivial evals cs0
      cs = map sort cs1
  printf "%d classes, %d raw equations, %d tests.\n"
         (length cs)
         (sum (map (subtract 1 . length) cs))
         (n*50)
  return (n, cs)

memoSym :: Context -> (Symbol -> a) -> (Symbol -> a)
memoSym ctx f = (arr !) . label
  where arr = listArray (0, length ctx - 1) (map f ctx)

tests :: Int -> Context -> ([Term Symbol] -> Bool) -> [(StdGen, Int)] -> Int -> IO (Int, [[Term Symbol]])
tests 0 _ _ _ _ = return (0, [])
tests (d+1) ctx trivial vals start = do
  (n0, cs0) <- tests d ctx (const False) vals start
  let reps = map head cs0
      base ty = [ t | t <- reps, termType t == ty ]
  (n, cs) <- test (d+1) ctx trivial vals start base
  (_, cs1) <- tests d ctx (const False) vals n
  if cs0 == cs1 then return (n, cs) else tests (d+1) ctx trivial vals n
