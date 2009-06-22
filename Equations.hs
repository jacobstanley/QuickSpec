{-# LANGUAGE GADTs #-}
module Main where

import Control.Monad.State
import Control.Monad.Writer
import Data.List
import Data.Maybe
import Data.Ord
import Data.Typeable
import System.IO
import System.IO.Unsafe(unsafeInterleaveIO)
import System.Random
import Test.QuickCheck hiding (label)
import Test.QuickCheck.Gen
import Text.Printf
import Term
import CongruenceClosure hiding (newSym)

-- Context

type Context = [Symbol]
type Universe = TypeRep -> [Term Symbol]

resultTypes :: TypeRep -> [TypeRep]
resultTypes ty =
  case splitTyConApp ty of
    (c, [_, ty']) | tyConString c == "->" -> ty:resultTypes ty'
    _ -> [ty]

allTypes :: Context -> [TypeRep]
allTypes ctx = nub (concatMap (resultTypes . symbolType) ctx)

argTypes :: Context -> TypeRep -> [TypeRep]
argTypes ctx ty = [ ty1 | funcTy <- allTypes ctx,
                          (c, [ty1, ty2]) <- [splitTyConApp funcTy],
                          tyConString c == "->",
                          ty2 == ty ]

--

terms :: Context -> Universe -> Universe
terms ctx base ty =
     [ sym elt
     | elt <- ctx
     , symbolType elt == ty
     , let sym = if isVar elt then Var else Const
     ]
  ++ [ App f x
     | ty' <- argTypes ctx ty
     , x  <- base ty'
     , f  <- terms ctx base (mkFunTy ty' ty)
     ]

--

iterateUntil :: Eq b => Int -> (a -> b) -> (a -> a) -> a -> (Int, a)
iterateUntil start p f x = extract (head (filter eq (drop start (zip3 xs (tail xs) [0..]))))
    where xs = iterate f x
          eq (a, b, _) = p a == p b
          extract (x, _, n) = (n, x)

refine :: Ord b => Int -> Int -> (a -> [b]) -> [[a]] -> (Int, [[a]])
refine start step eval xss = flatten (iterateUntil start lengths refine1 ([], map (map (\x -> (x, eval x))) xss))
    where flatten (n, (triv, nontriv)) = (n, map (map fst) (triv ++ nontriv))
          refine1 (triv, nontriv) =
              let
                (triv', nontriv') = partition trivial (concatMap split nontriv)
              in
                (triv ++ triv', nontriv')
          lengths (xs, ys) = length xs + length ys
          first (x, vs) = take step vs
          next (x, vs) = (x, drop step vs)
          trivial [] = True
          trivial [_] = True
          trivial _ = False
          split xs = map (map next) (groupBy (\a b -> first a == first b)
                                             (sortBy (comparing first) xs))

--

varDepths d (App s t) = varDepths d s `merge` varDepths (d-1) t
varDepths d (Var x)   = [(x,d)]
varDepths d _         = []
  
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
            s <- mapM substs (varDepths d t)
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

instOf :: Term Symbol -> Term Symbol -> Maybe [(Symbol,Term Symbol)]
x `instOf` y = [x] `instOfL` [y]

instOfL :: [Term Symbol] -> [Term Symbol] -> Maybe [(Symbol,Term Symbol)]
xs `instOfL` ys = comp [] (zip ys xs)
 where
  comp sub []                                 = Just sub
  comp sub ((Var s,t):ps)                     = compSub sub s t ps
  comp sub ((Const s,t):ps) | t == Const s    = comp sub ps
                            | otherwise       = Nothing
  comp sub ((App f x, App g y):ps)            = comp sub ([(f, g), (x, y)] ++ ps)
  comp _   _                                  = Nothing

  compSub sub v t ps =
    case [ t' | (v',t') <- sub, v == v' ] of
      []             -> comp ((v,t):sub) ps
      t':_ | t == t' -> comp sub ps
      _              -> Nothing

subst :: [(Symbol, Term a)] -> Term a -> Term a
subst sub (App s t) = App (subst sub s) (subst sub t)
subst sub t@(Var s) = head ([ t | (v,t) <- sub, s == v ] ++ [ t ])
subst sub s         = s

--

bools = [
 var "x" False,
 var "y" False,
 var "z" False,
 con "&&" (&&),
 con "||" (||),
 con "not" not
 ]

--main :: IO ()
main =
  do hSetBuffering stdout NoBuffering
     laws bools 3

genSeeds :: IO [(StdGen, Int)]
genSeeds = do
  rnd <- newStdGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..20])))

laws ctx0 depth = do
  let ctx = zipWith relabel [0..] ctx0
  putStrLn "== API =="
  putStrLn "-- functions"
  sequence_ [ putStrLn (show (Const elt) ++ " :: " ++ show (symbolType elt))
            | elt <- ctx
            , isCon elt
            ]
  putStrLn "-- variables"
  sequence_ [ putStrLn (name elt ++ " :: " ++ show (symbolType elt))
            | elt <- ctx
            , isVar elt
            ]
  seeds <- genSeeds
  putStrLn "== classes =="
  (_, cs) <- tests depth ctx seeds 0
  let eqs = map head
          $ group
          $ sort
          $ [ (y,x) | (x:xs) <- cs, y <- xs ]
  printf "%d raw equations.\n\n" (length eqs)
--  let univ = concat [allTerms depth ctx t | t <- allTypes ctx]
  let univ = map head cs
  printf "Universe has %d terms.\n" (length univ)
  putStrLn "== equations =="
  let pruned = prune ctx depth univ eqs
  sequence_
       [ putStrLn (show y ++ " = " ++ show x)
       | (y,x) <- pruned
       ]
  forM pruned $ \(y, x) -> do
    let xs `isSubsetOf` ys = sort xs `isSublistOf` sort ys
        [] `isSublistOf` _ = True
        (x:xs) `isSublistOf` [] = False
        (x:xs) `isSublistOf` (y:ys) | x == y = xs `isSublistOf` ys
                                    | otherwise = (x:xs) `isSublistOf` ys
    when (not (vars y `isSubsetOf` vars x || vars x `isSubsetOf` vars y)) $
         printf "*** missing term with value %s\n"
                (show (mapVars (\s -> if s `elem` vars y then s else s { name = "_" ++ name s }) x))

test :: Int -> Context -> [(StdGen, Int)] -> Int -> (TypeRep -> [Term Symbol]) -> IO (Int, [[Term Symbol]])
test depth ctx seeds start base = do
  printf "Depth %d: " depth
  let cs0 = filter (not . null) [ terms ctx base ty | ty <- allTypes ctx ]
  printf "%d terms, " (length (concat cs0))
  let evalM x = do
        evalSym <- promote value
        case eval evalSym x of
          Data v -> fmap Inject (evaluate v)
      eval' x = [ unGen (evalM x) rnd n | (rnd, n) <- seeds ]
      (n, cs1) = refine start 50 eval' cs0
      cs = map sort cs1
  printf "%d classes, %d raw equations, %d tests.\n"
         (length cs)
         (sum (map (subtract 1 . length) cs))
         (n*50)
  return (n, cs)

tests :: Int -> Context -> [(StdGen, Int)] -> Int -> IO (Int, [[Term Symbol]])
tests 0 _ _ _ = return (0, [])
tests (d+1) ctx vals start = do
  (n0, cs0) <- tests d ctx vals start
  let reps = map head cs0
      base ty = [ t | t <- reps, termType t == ty ]
  (n, cs) <- test (d+1) ctx vals start base
  (_, cs1) <- tests d ctx vals n
  if cs0 == cs1 then return (n, cs) else tests (d+1) ctx vals n

data UntypedCompare where
  Inject :: (Typeable a, Ord a) => a -> UntypedCompare
instance Eq UntypedCompare where
  x == y = x `compare` y == EQ
instance Ord UntypedCompare where
  Inject x `compare` Inject y =
    case cast x of
      Just x' -> x' `compare` y
      Nothing -> error "incomparable"