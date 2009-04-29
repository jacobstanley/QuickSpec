module Main where

import Control.Monad
import Control.Monad.Writer
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Ord
import System.IO
import System.IO.Unsafe(unsafeInterleaveIO)
import System.Random
import Text.Printf
import Term
import CongruenceClosure

-- Context

type Context
  = [Symbol]

eval :: Context -> Term Symbol -> Data
eval ctx (Const s) = head ([ fromJust (what elt) | elt <- ctx, name elt == show s ] ++ error ("eval, no " ++ show s))
eval ctx (Var s) = head ([ fromJust (what elt) | elt <- ctx, name elt == show s ] ++ error ("eval, no " ++ show s))
eval ctx (App s t) = case eval ctx s of
                       Fun f -> f (eval ctx t)

allTypes :: Context -> [Type]
allTypes ctx = nub
  [ t
  | elt <- ctx
  , let tps r@(s :-> t) = r:(tps s ++ tps t)
        tps t         = t : case t of
                              TCon _ t' -> tps t'
                              _         -> []
  , t <- tps (typ elt)
  ]

eqTypes :: Context -> [Type]
eqTypes ctx = filter isEq (allTypes ctx)
    where
        isEq (Simple _) = True
        isEq (TCon _ t) = isEq t
        isEq _          = False

-- example context

list :: Type -> Type
list t = TCon "[]" t

a, int, bool :: Type
a    = Simple "A"
int  = Simple "Int"
bool = Simple "Bool"

infix 3 =::
infix 2 =:

(=::) :: String -> Type -> Symbol
x =:: t = Symbol { name = x, typ = t, label = undefined, what = Nothing }

(=:) :: Symbol -> Data -> Symbol
elt =: impl = elt{ what = Just impl }

xs = "xs" =:: list a
ys = "ys" =:: list a
zs = "zs" =:: list a

x = "x" =:: int
y = "y" =:: int
z = "z" =:: int

a1 = "a" =:: a
b  = "b" =:: a
c  = "c" =:: a

b1 = "a" =:: bool
b2 = "b" =:: bool
b3 = "c" =:: bool

f = "f" =:: a :-> a
g = "g" =:: a :-> a

plus = "+" =:: int :-> int :-> int
    =: Fun (\(Int x) -> Fun (\(Int y) -> Int (x + y)))

mult = "*" =:: int :-> int :-> int
    =: Fun (\(Int x) -> Fun (\(Int y) -> Int (x * y)))

app = "++" =:: list a :-> list a :-> list a
    =: Fun (\(List xs) -> Fun (\(List ys) -> List (xs ++ ys)))

cons = ":" =:: a :-> list a :-> list a
     =: Fun (\x -> Fun (\(List ys) -> List (x : ys)))

rev = "reverse" =:: list a :-> list a
    =: Fun (\(List xs) -> List (reverse xs))

tak = "take" =:: int :-> list a :-> list a
    =: Fun (\(Int k) -> Fun (\(List xs) -> List (take k xs)))

drp = "drop" =:: int :-> list a :-> list a
    =: Fun (\(Int k) -> Fun (\(List xs) -> List (drop k xs)))

srt = "sort" =:: list a :-> list a
    =: Fun (\(List xs) -> List (sort xs))

nul = "null" =:: list a :-> bool
    =: Fun (\(List xs) -> Bool (null xs))

isP = "isPrefixOf" =:: list a :-> list a :-> bool
    =: Fun (\(List xs) -> Fun (\(List ys) -> Bool (xs `isPrefixOf` ys)))

bnot = "not" =:: bool :-> bool
     =: Fun (\(Bool a) -> Bool (not a))

impl = "->" =:: bool :-> bool :-> bool
     =: Fun (\(Bool a) -> Fun (\(Bool b) -> Bool (not a || b)))

bor  = "||" =:: bool :-> bool :-> bool
     =: Fun (\(Bool a) -> Fun (\(Bool b) -> Bool (a || b)))

band = "&&" =:: bool :-> bool :-> bool
     =: Fun (\(Bool a) -> Fun (\(Bool b) -> Bool (a && b)))

true = "True" =:: bool
     =: Bool True

false = "False" =:: bool
     =: Bool False

zero = "0" =:: int =: Int 0
one = "1" =:: int =: Int 1

nil  = "[]" =:: list a
     =: List []

mapp = "map" =:: (a :-> a) :-> list a :-> list a
     =: Fun (\(Fun f) -> Fun (\(List xs) -> List (map f xs)))

comp = "." =:: (a :-> a) :-> (a :-> a) :-> (a :-> a)
     =: Fun (\(Fun f) -> Fun (\(Fun g) -> Fun (f . g)))

lists :: Context
lists = [ nil, app, rev, srt, xs, ys, zs ]

lists' :: Context
lists' = [ nil, app, rev, srt, xs ]

ints :: Context
ints = [ plus, mult, x, y, z, zero, one ]

bools :: Context
bools = [ bor, band, bnot, false, true, b1, b2, b3 ]

bools2 = [ band, b1, b2 ]

--

terms :: [Symbol] -> (Type -> [Term Symbol]) -> Type -> [Term Symbol]
terms ctx base t =
     [ sym elt
     | elt <- ctx
     , typ elt == t
     , let sym = if isVar elt then Var else Const
     ]
  ++ [ App f x
     | t' <- argtypes ctx t
     , x  <- base t'
     , f  <- terms ctx base (t' :-> t)
     ]
 where
  argtypes ctx t =
    nub
    [ t1
    | elt <- ctx
    , t1 :-> t2 <- funs (typ elt)
    , t == t2
    ]
  
  funs (s :-> t) = (s :-> t) : funs t
  funs _         = []

allTerms :: Int -> [Symbol] -> Type -> [Term Symbol]
allTerms 0 ctx ty = []
allTerms (n+1) ctx ty = terms ctx (allTerms n ctx) ty

--

iterateUntil :: Eq b => (a -> b) -> (a -> a) -> a -> (Int, a)
iterateUntil p f x = extract (head (filter eq (zip3 xs (tail xs) [0..])))
    where xs = iterate f x
          eq (a, b, _) = p a == p b
          extract (x, _, n) = (n, x)

refine :: Ord b => Int -> (a -> [b]) -> [[a]] -> (Int, [[a]])
refine step eval xss = flatten (iterateUntil lengths refine1 ([], map (map (\x -> (x, eval x))) xss))
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

gens :: Context -> IO [Context]
gens ctx = unsafeInterleaveIO $ do
             ctx' <- gen ctx
             ctxs <- gens ctx
             return (ctx':ctxs)

gen :: Context -> IO Context
gen ctx =
  sequence
    [ case what elt of
        Just _  -> do return elt
        Nothing -> do a <- genType (typ elt)
                      return elt{ what = Just a }
    | elt <- ctx
    ]

genInt :: IO Int
genInt = 
  do k <- genNat
     n <- randomRIO (-(k*k),k*k)
     return n

genNat :: IO Int
genNat = 
  do n <- randomRIO (0,100)
     k <- randomRIO (0,n)
     randomRIO (0,k)

-- this is a big hack for now
genType :: Type -> IO Data
genType (Simple "A") =
  do n <- genNat
     return (Int n)

genType (Simple "Int") =
  do n <- genInt
     return (Int n)

genType (Simple "Bool") =
  do n <- randomRIO (0,1 :: Int)
     return (Bool (even n))

genType (TCon "[]" t) =
  do k <- genNat
     xs <- sequence [ genType t | i <- [1..k] ]
     return (List xs)

genType (Simple "Int" :-> t) =
  do k  <- (1+) `fmap` genNat
     ys <- sequence [ genType t | i <- [0..k*k] ]
     return (Fun (\(Int x) -> ys !! (x `mod` (k*k))))

genType (Simple "A" :-> t) =
  do k  <- (1+) `fmap` genNat
     ys <- sequence [ genType t | i <- [0..k*k] ]
     return (Fun (\(Int x) -> ys !! (x `mod` (k*k))))

genType t =
  error ("could not generate a " ++ show t)

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

consequences :: Int -> [(Int, Int, Type)] -> (Term Int, Term Int) -> CC () ()
consequences d univ (t, u) = mapM_ unify (cons1 t u `mplus` cons1 u t)
    where unify (x, y) = do
            x' <- flatten x
            y' <- flatten y
            x' =:= y'
          cons1 t u = do
            s <- mapM substs (varDepths d t)
            return (subst s t, subst s u)
          substs (v, d) = [ (v, Const s) | (_, s, ty) <- takeWhile (\(d', _, _) -> d' <= d) univ, ty == typ v ]

flatten (Var s) = return (label s)
flatten (Const s) = return s
flatten (App t u) = do
  t' <- flatten t
  u' <- flatten u
  t' $$ u'

killSymbols (Var s) = Var s
killSymbols (Const s) = Const (label s)
killSymbols (App t u) = App (killSymbols t) (killSymbols u)

prune1 :: Int -> [(Int, Int, Type)] -> [(Term Symbol, Term Symbol)] -> CC () [(Term Symbol, Term Symbol)]
prune1 d univ es = fmap snd (runWriterT (mapM_ (consider univ) es))
    where consider univ (t, u) = do
            b <- lift (canDerive t u)
            when (not b) $ do
              tell [(t, u)]
              lift (consequences d univ (killSymbols t, killSymbols u))

prune2 :: Int -> [(Int, Int, Type)] -> [(Term Symbol, Term Symbol)] -> [(Term Symbol, Term Symbol)] -> CC () [(Term Symbol, Term Symbol)]
prune2 d univ committed [] = return committed
prune2 d univ committed ((t,u):es) = do
  b <- frozen $ do
         forM_ (committed ++ es) $ \(t, u) -> consequences d univ (killSymbols t, killSymbols u)
         canDerive t u
  if b then prune2 d univ committed es
       else prune2 d univ ((t,u):committed) es

loadUniv :: [Term Symbol] -> CC a [(Int, Int, Type)]
loadUniv univ = fmap (sortBy (comparing (\(d,_,_) -> d))) (mapM f univ)
    where f t = do
            t' <- flatten (killSymbols t)
            return (depth t, t', typeOf t)

prune :: Context -> Int -> [Term Symbol] -> [(Term Symbol, Term Symbol)] -> [(Term Symbol, Term Symbol)]
prune ctx d univ0 es = runCCctx ctx $ do
  univ <- loadUniv univ0
  es' <- frozen (prune1 d univ es)
  prune2 d univ [] (reverse (sort es'))

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

alphaRename :: Context -> (Term Symbol,Term Symbol) -> (Term Symbol,Term Symbol)
alphaRename ctx (x,y)
  | x' < y'   = (y',x')
  | otherwise = (x',y')
 where
  x' = subst sub x
  y' = subst sub y
 
  vs = nub (vars x ++ vars y)
  sub = [ (v, Var (alpha v))
        | v <- vs
        ]
  alpha v =
    head
    [ newv
    | (oldv,newv) <- [ w | w <- vs, typ w == typ v ]
               `zip` [ elt | elt <- ctx, isNothing (what elt), typ elt == typ v ]
    , v == oldv
    ]

--

--main :: IO ()
main =
  do hSetBuffering stdout NoBuffering
     laws bools 3

laws ctx0 depth = do
  let ctx = zipWith relabel [0..] ctx0
  putStrLn "== API =="
  putStrLn "-- functions"
  sequence_ [ putStrLn (show (Const elt) ++ " :: " ++ show (typ elt))
            | elt <- ctx
            , not (isNothing (what elt))
            ]
  putStrLn "-- variables"
  sequence_ [ putStrLn (name elt ++ " :: " ++ show (typ elt))
            | elt <- ctx
            , isNothing (what elt)
            ]
  vals <- gens ctx
  putStrLn "== classes =="
  (_, cs) <- bind [testGen i ctx vals . snd | i <- [1..depth-1]] (undefined, const []) >>= test depth ctx vals . snd
  let eqs = map head
          $ group
          $ sort
          $ map (alphaRename ctx)
          $ [ (y,x) | (x:xs) <- cs, y <- xs ]
  printf "After alpha renaming: %d raw equations.\n\n" (length eqs)
--  let univ = concat [allTerms depth ctx t | t <- allTypes ctx]
  let univ = concat cs
  printf "Universe has %d terms.\n" (length univ)
  putStrLn "== equations =="
  sequence_
       [ putStrLn (show y ++ " = " ++ show x)
       | (y,x) <- prune ctx depth univ eqs
       ]

bind [] x = return x
bind (f:fs) x = f x >>= bind fs

test :: Int -> Context -> [Context] -> (Type -> [Term Symbol]) -> IO (Int, [[Term Symbol]])
test depth ctx vals base = do
  printf "Depth %d: " depth
  let cs0 = filter (not . null) [ terms ctx base ty | ty <- eqTypes ctx ]
  printf "%d terms, " (length (concat cs0))
  let eval' x = [ eval val x | val <- vals ]
      (n, cs1) = refine 50 eval' cs0
      cs = map sort cs1
  printf "%d classes, %d raw equations, %d tests.\n"
         (length cs)
         (sum (map (subtract 1 . length) cs))
         (n*50)
  return (n*50, cs)

testGen :: Int -> Context -> [Context] -> (Type -> [Term Symbol]) -> IO (Int, Type -> [Term Symbol])
testGen depth ctx vals base = do
  fmap (\(n, cs) -> (n, \ty -> [ t | (t:_) <- cs, typeOf t == ty])) (test depth ctx vals base)
