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
import Term
import TermCongruenceClosure

-- Context

type Context
  = [Symbol]

eval :: Context -> Term Symbol -> Data
eval ctx (Const s) = head ([ fromJust (what elt) | elt <- ctx, name elt == show s ] ++ error ("eval, no " ++ show s))
eval ctx (Var v)   = error "ground term needed"
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
ints = [ plus, mult, x, y, z ]

bools :: Context
bools = [ bor, band, bnot, false, true, b1, b2, b3 ]

bools2 = [ band, b1, b2 ]

--

terms :: Context -> Int -> Int -> Type -> [Term Symbol]
terms ctx d s t =
     [ sym elt
     | d >= 1 && s >= 1
     , elt <- ctx
     , typ elt == t
     , let sym = if isVar elt then Var else Const
     ]
  ++ [ App f x
     | d >= 1 && s >= 2
     , t' <- argtypes ctx t
     , x  <- terms ctx (d-1) (s-1)      t'
     , f  <- terms ctx d     (s-size x) (t' :-> t)
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

--

iterateUntil :: Eq b => (a -> b) -> (a -> a) -> a -> a
iterateUntil p f x = fst (head (filter eq (zip xs (tail xs))))
    where xs = iterate f x
          eq (a, b) = p a == p b

refine :: Ord b => Int -> (a -> [b]) -> [a] -> [[a]]
refine step eval xs = flatten (iterateUntil lengths refine1 ([], [[ (x, eval x) | x <- xs ]]))
    where flatten (triv, nontriv) = map (map fst) (triv ++ nontriv)
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

refine' :: Context -> [Term Symbol] -> IO [[Term Symbol]]
refine' ctx xs = do
  ctxs <- gens ctx
  let f x = [ eval ctx x | ctx <- ctxs ]
  return (refine 50 f xs)

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

consequences :: [Term Symbol] -> (Term Symbol, Term Symbol) -> TCC ()
consequences univ (t, u) = mapM_ unify (cons1 t u `mplus` cons1 u t)
    where unify (x, y) = x =:= y
          cons1 t u = do
            a <- univ
            s <- maybeToList (a `instOf` t)
            let b = subst s u
            return (a, b)
            
prune :: [Symbol] -> [Term Symbol] -> [(Term Symbol, Term Symbol)] -> [(Term Symbol, Term Symbol)]
prune ctx univ es = snd (runTCC ctx (runWriterT (mapM_ consider es)))
    where consider (t, u) = do
            b <- lift (t =?= u)
            when (not b) $ do
              tell [(t, u)]
              lift (consequences univ (t, u))

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

subst :: [(Symbol,Term Symbol)] -> Term Symbol -> Term Symbol
subst sub (App s t) = App (subst sub s) (subst sub t)
subst sub t@(Var s) = head ([ t | (v,t) <- sub, s == v ] ++ [ t ])
subst sub s         = s

--

alphaRename :: Context -> (Term Symbol,Term Symbol,Type) -> (Term Symbol,Term Symbol,Type)
alphaRename ctx (x,y,t)
  | x' < y'   = (y',x',t)
  | otherwise = (x',y',t)
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
     eqs bools (3,7) (3,7)

--eqs :: Context -> (Int,Int) -> (Int,Int) -> IO ()
eqs ctx0 (eqd,eqs) (und,uns) =
  do putStrLn "== API =="
     putStrLn "-- functions"
     let ctx = zipWith relabel [0..] ctx0
     sequence_ [ putStrLn (show (Const elt) ++ " :: " ++ show (typ elt))
               | elt <- ctx
               , not (isNothing (what elt))
               ]
     putStrLn "-- variables"
     sequence_ [ putStrLn (name elt ++ " :: " ++ show (typ elt))
               | elt <- ctx
               , isNothing (what elt)
               ]
     putStrLn "== types =="
     putStrLn ("-- depth <= " ++ show eqd ++ ", size <= " ++ show eqs)
     let trms = [ (t, xs) | t <- eqTypes ctx, let xs = terms ctx eqd eqs t, not (null xs) ]
     sequence_
       [ do putStrLn (show t ++ ": " ++ show (length xs) ++ " terms")
            -- sequence_ [ putStrLn (show x) | x <- xs ]
       | (t, xs) <- trms
       ]
     putStrLn "== classes =="
     clss <- sequence
               [ do xss <- refine' ctx xs
                    putStrLn (show t ++ ": " ++ show (length xss) ++ " classes, "
                                             ++ show (sum [ length xs | (x:xs) <- xss]) ++ " raw equations")
                    return (t, map sort xss)
               | (t,xs) <- trms
               ]
     let eqs  = map head
              $ group
              $ sortBy (comparing (\(x,y,t) -> (x,y)))
              $ map (alphaRename ctx)
              $ [ (y,x,t) | (t, xss) <- clss, (x:xs) <- xss, y <- xs ]
     putStrLn ("-- after alpha renaming: " ++ show (length eqs) ++ " raw equations")
     {-
     sequence_
       [ putStrLn (show y ++ " = " ++ show x)
       | (y,x) <- eqs
       ]
     -}
     putStrLn "== equations =="
     let univ = concat [terms ctx und uns t | t <- allTypes ctx]
     sequence_
       [ putStrLn (show y ++ " = " ++ show x)
       | (y,x) <- prune ctx univ (map (\(x,y,_) -> (x,y)) eqs)
       ]
     return (univ, map (\(x,y,_) -> (x,y)) eqs)