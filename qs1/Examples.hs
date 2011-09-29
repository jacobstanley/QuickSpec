{-# OPTIONS_GHC -fno-warn-deprecated-flags #-}
{-# LANGUAGE ScopedTypeVariables,DeriveDataTypeable,TypeFamilies,GeneralizedNewtypeDeriving,TypeSynonymInstances,StandaloneDeriving,FlexibleInstances,FlexibleContexts,UndecidableInstances,PatternSignatures #-}

module Main where

import Prelude hiding (read)
import Equations hiding (merge, evaluate)
import Term
import qualified Data.List
import Data.Maybe
import Data.Ord
import Data.Typeable
import Test.QuickCheck
import System.Environment hiding (getEnv)
import System.Random
import Control.Arrow
import Control.Monad
import Control.Monad.State.Strict
import PrettyPrinting
import Regex hiding (State, run)
import qualified TinyWM as T
import qualified TinyWMProperties as TP
import qualified Data.Map as M
import qualified Regex
import qualified Arrays

bools = describe "bools" [
 var "x" False,
 var "y" False,
 var "z" False,
 con " && " (&&),
 con " || " (||),
 con "not" not,
-- con "=>" (\x y -> not x || y),
 con "True" True,
 con "False" False
 ]

base = [
 var "x" (undefined :: Elem),
 var "y" (undefined :: Elem),
 var "z" (undefined :: Elem),
 var "i" int,
 var "j" int,
 var "n" int ]
  where int :: Int
        int = undefined

lists = describe "lists" [
 var "xs" list,
 var "ys" list,
 var "zs" list,
 con " ++ " ((++) :: [Elem] -> [Elem] -> [Elem]),
-- con "reverse" (reverse :: [Elem] -> [Elem]),
 con "head" (head :: [Elem] -> Elem),
 con "tail" (tail :: [Elem] -> [Elem]),
 con " : " ((:) :: Elem -> [Elem] -> [Elem]),
 con "[]" ([] :: [Elem]),
 --con "sort" (Data.List.sort :: [Elem] -> [Elem]),
 --con "nub" (Data.List.nub :: [Elem] -> [Elem]),
-- con "mergeL" mergeL,
 --con "unit" (\x -> [x] :: [Elem]),
-- con "insertL" (Data.List.insert :: Int -> [Int] -> [Int]),
 con "null" (null :: [Elem] -> Bool)]
  where list :: [Elem]
        list = undefined

data Monotonic = Monotonic Int (Int -> Int) deriving Typeable
instance Arbitrary Monotonic where
  arbitrary = liftM2 Monotonic arbitrary arbitrary

instance Classify Monotonic where
  type Value Monotonic = Int
  evaluate m = evaluate (monotonic m)

instance Show Monotonic where
  show (Monotonic base f) = show (base, zip [-20..20] $ map f [-20..20])

monotonic :: Monotonic -> Int -> Int
monotonic _ n | n >= 500 || n < -500 = error "oops"
monotonic (Monotonic base f) n | n >= 0 = base + sum [ abs (f i) | i <- [0 .. n-1] ]
                               | otherwise = base - sum [ abs (f i) | i <- [n..negate 1] ]

prop_monotonic m = Data.List.sort xs == xs
  where xs = map (monotonic m) [-20..20]

prop_false m = Data.List.nub xs /= xs
  where xs = map (monotonic m) [-20..20]

mergeL :: [Int] -> [Int] -> [Int]
mergeL [] xs = xs
mergeL xs [] = xs
mergeL (x:xs) (y:ys) | x < y = x:mergeL xs (y:ys)
                    | otherwise = y:mergeL (x:xs) ys

-- Leftist heaps.
data Heap a = Nil | Branch Int a (Heap a) (Heap a) deriving Typeable

instance Ord a => Eq (Heap a) where
  h1 == h2 = toList h1 == toList h2

instance Ord a => Ord (Heap a) where
  compare = comparing toList

instance (Ord a, Arbitrary a) => Arbitrary (Heap a) where
  arbitrary = fmap fromList arbitrary

instance (Classify a, Ord a) => Classify (Heap a) where
  type Value (Heap a) = [Value a]
  evaluate = evaluate . toList

toList :: Ord a => Heap a -> [a]
toList h | empty h = []
         | otherwise = top h:toList (delete h)

toList' :: Heap a -> [a]
toList' Nil = []
toList' (Branch _ x l r) = x:(toList' l ++ toList' r)

fromList :: Ord a => [a] -> Heap a
fromList = foldr insert Nil

empty :: Heap a -> Bool
empty Nil = True
empty _ = False

top :: Heap a -> a
top (Branch _ x _ _) = x

insert :: Ord a => a -> Heap a -> Heap a
insert x h = merge h (branch x Nil Nil)

delete :: Ord a => Heap a -> Heap a
delete (Branch _ _ l r) = merge l r

branch :: Ord a => a -> Heap a -> Heap a -> Heap a
branch x l r | npl l <= npl r = Branch (npl l + 1) x l r
             | otherwise = Branch (npl r + 1) x r l

merge :: Ord a => Heap a -> Heap a -> Heap a
merge Nil h = h
merge h Nil = h
merge h1@(Branch _ x1 l1 r1) h2@(Branch _ x2 l2 r2)
 | x1 <= x2 = branch x1 (merge l1 h2) r1
 | otherwise = merge h2 h1

leftBranch (Branch _ _ l _) = l
rightBranch (Branch _ _ _ r) = r

npl :: Heap a -> Int
npl Nil = 0
npl (Branch n _ _ _) = n

heaps = describe "heaps" [
 var "h" (Nil :: Heap Elem),
 var "h1" (Nil :: Heap Elem),
 var "h2" (Nil :: Heap Elem),
 con "toList" (\h -> toList h :: [Elem]),
 con "fromList" (\xs -> fromList xs :: Heap Elem),
 con "isEmpty" (\h -> empty (h :: Heap Elem)),
 con "findMin" (\h -> top h :: Elem),
 con "insert" (\x h -> insert x h :: Heap Elem),
 con "deleteMin" (\h -> delete h :: Heap Elem),
 con "merge" (\h1 h2 -> merge h1 h2 :: Heap Elem),
 con "empty" (Nil :: Heap Elem)
-- con "leftBranch" (leftBranch :: Heap Elem -> Heap Elem),
-- con "rightBranch" (rightBranch :: Heap Elem -> Heap Elem)
 ]


nats = describe "nats" [
 con " + " ((+) :: Int -> Int -> Int),
-- con " - " ((-) :: Int -> Int -> Int),
 con " * " ((*) :: Int -> Int -> Int),
 con "neg" (negate :: Int -> Int),
 con "0" (0 :: Int),
 con "1" (1 :: Int) ]

type StackSet = T.StackSet Elem

newtype Elem = Elem Int deriving (Arbitrary, CoArbitrary, Eq, Ord, Typeable, Show)
instance Classify Elem where
  type Value Elem = Elem
  evaluate = return

instance Classify Ordering where
  type Value Ordering = Ordering
  evaluate = return

instance Classify StackSet where
  type Value StackSet = StackSet
  evaluate = return

tinywm = describe "tinywm" [
 con "empty" (T.empty :: Int -> StackSet),
 con "view" (T.view :: Int -> StackSet -> StackSet),
 con "peek" (fromJust . T.peek :: StackSet -> Elem),
 con "rotate" (T.rotate :: Ordering -> StackSet -> StackSet),
 con "push" (T.push :: Elem -> StackSet -> StackSet),
 con "shift" (T.shift :: Int -> StackSet -> StackSet),
 con "insert" (T.insert :: Elem -> Int -> StackSet -> StackSet),
 con "delete" (T.delete :: Elem -> StackSet -> StackSet),
 con "index" (T.index :: Int -> StackSet -> [Elem]),
 var "s" (undefined :: StackSet),
 con "LT" LT,
 con "GT" GT,
 con "EQ" EQ,
 var "o" (undefined :: Ordering),
 var "o'" (undefined :: Ordering)]

examples = [
 ("nats",      (base ++ nats,                    True,  const True,  allOfThem)),
 ("bools",     (base ++ bools,                   True,  const True,  allOfThem)),
 ("lists",     (base ++ bools ++ lists,          True,  const True,  about ["lists"])),
 ("heaps",     (base ++ bools ++ lists ++ heaps, False, const True,  about ["heaps"])),
 ("arrays",    (base ++ arrays,                  True,  const True,  allOfThem)),
 ("comp",      (base ++ comp,                    False, const True,  allOfThem)),
 ("queues",    (base ++ bools ++ queues,         True,  const True,  about ["queues"])),
 ("queuesM",   (queuesM,                         False, noRebinding, about ["queuesM"])),
-- ("arraysM", (arraysM,                         False, noRebinding, about ["arraysM"])),
 ("pretty",    (base ++ nats ++ pretty,          False, const True,  about ["pretty"])),
 ("regex",     (regex,                           False, const True,  allOfThem)),
 ("tinywm",    (base ++ lists ++ tinywm,         True,  const True,  about ["tinywm"]))
 ]

data Sym = A | B deriving (Eq, Ord, Typeable)

instance Arbitrary Sym where
  arbitrary = elements [A, B]

instance Classify Sym where
  type Value Sym = Sym
  evaluate = return

regex = [
 var "x" A,
 var "y" A,
 var "z" A,
 var "r" (Char A),
 var "s" (Char A),
 var "t" (Char A),
 con "char" (Char :: Sym -> Regex Sym),
 con "any" (AnyChar :: Regex Sym),
 con "ε" (Epsilon :: Regex Sym),
 con "0" (Zero :: Regex Sym),
 con ";" (Concat :: Regex Sym -> Regex Sym -> Regex Sym),
 con "|" (Choice :: Regex Sym -> Regex Sym -> Regex Sym),
 con "*" (star :: Regex Sym -> Regex Sym) ]

instance Arbitrary (Regex Sym) where
  arbitrary = sized arb
    where arb 0 = oneof [fmap Char arbitrary, return AnyChar, return Epsilon, return Zero]
          arb n = oneof [fmap Char arbitrary, return AnyChar, return Epsilon, return Zero,
                         liftM2 Concat arb' arb', liftM2 Choice arb' arb', fmap Plus (arb (n-1))]
            where arb' = arb (n `div` 2)

instance Classify (Regex Sym) where
  type Value (Regex Sym) = Bool
  evaluate r = do
    s <- arbitrary
    return (Regex.run (compile r) s)

main = do
  args <- getArgs
  let test = case args of
               [] -> "bools"
               [x] -> x
      Just (cons, cond, p, p') = lookup test examples
  laws 3 cons cond p p'
  --congruenceCheck 3 cons p

type ArrayM = State Arrays.Array

instance Classify a => Classify (ArrayM a) where
  type Value (ArrayM a) = (Value a, Arrays.Array)
  evaluate x = do
    a <- arbitrary
    let (r, a') = runState x a
    r' <- evaluate r
    return (r', a')

newA :: ArrayM ()
newA = put Arrays.new

getA :: Arrays.Index -> ArrayM Elem
getA = fmap Elem . gets . Arrays.get

setA :: Arrays.Index -> Elem -> ArrayM ()
setA ix (Elem v) = modify (Arrays.set ix v)

arrays = [
 var "a" (undefined :: Arrays.Array),
 var "i" (Arrays.Index undefined),
 var "j" (Arrays.Index undefined),
 var "k" (Arrays.Index undefined),
 con "new" Arrays.new,
 con "get" (\ix v -> Elem (Arrays.get ix v)),
 con "set" (\ix (Elem v) -> Arrays.set ix v),
 con "0" (Elem 0)
 ]

-- arraysM = describe "arraysM" [
--  (con "X" X) { typ = TVar },
--  (con "Y" Y) { typ = TVar },
--  (con "Z" Z) { typ = TVar },
--  var "x" (undefined :: Symbolic Elem),
--  var "y" (undefined :: Symbolic Elem),
--  var "z" (undefined :: Symbolic Elem),
-- -- var "i" (undefined :: Symbolic Index),
-- -- var "j" (undefined :: Symbolic Index),
-- -- var "k" (undefined :: Symbolic Index),
--  con "0" (Symbolic (const (Index 0)) :: Symbolic Index),
--  con "read" (read :: Var -> Symbolic Elem),
-- -- con "read" (read :: Var -> Symbolic Index),
--  con "return" (\x v -> symbolic (x :: Symbolic Elem) >>= write v :: Prog ArrayM ()),
--  con "return" (\x v -> symbolic (x :: Symbolic Index) >>= write v :: Prog ArrayM ()),
--  var "k" (undefined :: Prog ArrayM ()),
-- -- con "new" ((cps $ run newA)),
--  con "get" (\ix v -> cps $ symbolic ix >>= run . getA >>= write v),
--  con "set" (\ix x -> cps $ symbolic ix >>= \ix' -> symbolic x >>= run . setA ix')]

comp = [
 var "f" (undefined :: (Int -> Int)),
 var "g" (undefined :: (Int -> Int)),
 var "h" (undefined :: (Int -> Int)),
 con "." (\f g x -> f (g (x :: Int) :: Int) :: Int),
 con "id" (id :: Int -> Int)]

data Queue = Queue [Elem] [Elem] deriving (Typeable, Show)

instance Eq Queue where
  q1 == q2 = q1 `compare` q2 == EQ

instance Ord Queue where
  compare = comparing listQ

instance Arbitrary Queue where
  arbitrary = liftM2 Queue arbitrary arbitrary

instance Classify Queue where
  type Value Queue = [Elem]
  evaluate = return . listQ

deriving instance Typeable2 State

instance (Typeable s, Typeable1 m) => Typeable1 (StateT s m) where
  typeOf1 (_ :: StateT s m a) = mkTyConApp (mkTyCon "Control.Monad.State.StateT")
                                           [ typeOf (undefined :: s),
                                             typeOf1 (undefined :: m a) ]

listQ (Queue xs ys) = xs ++ reverse ys

new = Queue [] []
nullQ (Queue [] []) = True
nullQ _ = False

inl x (Queue xs ys) = Queue (x:xs) ys
inr y (Queue xs ys) = Queue xs (y:ys)
--outl (Queue (x:xs) ys) = Queue xs ys
outl = withLeft (\(x:xs) ys -> Queue xs ys)
outr = withRight (\xs (y:ys) -> Queue xs ys)
peekl = withLeft (\(x:xs) ys -> x)
peekr = withRight (\xs (y:ys) -> y)
withLeft f (Queue [] ys) = f (reverse ys) []
withLeft f (Queue xs ys) = f xs ys
withRight f (Queue xs []) = f [] (reverse xs)
withRight f (Queue xs ys) = f xs ys

type QueueM = State Queue

instance Classify a => Classify (QueueM a) where
  type Value (QueueM a) = (Value a, Queue)
  evaluate m = do
    q <- arbitrary
    let (x, q') = runState m q
    x' <- evaluate x
    return (x', q')

instance Classify () where
  type Value () = ()
  evaluate = return

newM :: QueueM ()
newM = put new

nullM :: QueueM Bool
nullM = gets nullQ

inlM, inrM :: Elem -> QueueM ()
inlM x = modify (inl x)
inrM x = modify (inr x)

outlM, outrM :: QueueM ()
outlM = modify outl
outrM = modify outr

peeklM, peekrM :: QueueM Elem
peeklM = gets peekl
peekrM = gets peekr

queues = describe "queues" [
 var "q" (Queue [] []),
 con "new" new,
 con "null" nullQ,
 con "inl" inl,
 con "inr" inr,
 con "outl" outl
-- con "outr" outr,
-- con "peekl" peekl,
-- con "peekr" peekr
 ]

newtype Stop a = Stop a deriving Typeable

instance Classify a => Classify (Stop a) where
  type Value (Stop a) = Value a
  evaluate (Stop x) = evaluate x

newtype Prog m a = Prog (StateT Env m a) deriving Monad

instance Typeable1 m => Typeable1 (Prog m) where
  typeOf1 (_ :: Prog m a) = mkTyConApp (mkTyCon "Prog") [ typeOf1 (undefined :: m a) ]

instance (Typeable1 m, Typeable a, Classify (m (a, Env))) => Classify (Prog m a) where
  type Value (Prog m a) = Value (m (a, Env))
  evaluate (Prog x) = do
    vars <- arbitrary
    evaluate (runStateT x vars)

instance Monad m => Arbitrary (Prog m ()) where
  arbitrary = return (return ())

type Env = (Vars Elem, Vars Arrays.Index)

values :: Typeable a => Env -> [a]
values (xs1, xs2) = catMaybes (map3 cast xs1 ++ map3 cast xs2)
  where map3 :: (a -> b) -> (a, a, a) -> [b]
        map3 f (x, y, z) = [f x, f y, f z]

class InEnv a where
  getEnv :: Env -> Vars a
  putEnv :: Vars a -> Env -> Env

instance InEnv Elem where
  getEnv = fst
  putEnv vs' (_, vs) = (vs', vs)

instance InEnv Arrays.Index where
  getEnv = snd
  putEnv vs' (vs, _) = (vs, vs')

read :: InEnv a => Var -> Symbolic a
read v = Symbolic (readV v . getEnv)

write :: (InEnv a, Monad m) => Var -> a -> Prog m ()
write v x = Prog (modify (\env -> putEnv (writeV v x (getEnv env)) env))

type Vars a = (Maybe a, Maybe a, Maybe a)
readV X (Just x, _, _) = x
readV Y (_, Just y, _) = y
readV Z (_, _, Just z) = z
writeV X x (Nothing, y, z) = (Just x, y, z)
writeV Y y (x, Nothing, z) = (x, Just y, z)
writeV Z z (x, y, Nothing) = (x, y, Just z)

data Var = X | Y | Z deriving (Typeable, Eq, Ord)

instance Arbitrary Var where
  arbitrary = elements [X, Y, Z]

instance Classify Var where
  type Value Var = Var
  evaluate = return

  validSubstitution _ s = nubSort (map snd s) == Data.List.sort (map snd s)

newtype Symbolic a = Symbolic (Env -> a) deriving Typeable

instance (Typeable a, Arbitrary a) => Arbitrary (Symbolic a) where
  arbitrary = fmap Symbolic (promote arb)
    where arb env = oneof (arbitrary:map return (values env))

instance Classify a => Classify (Symbolic a) where
  type Value (Symbolic a) = Value a
  evaluate (Symbolic f) = fmap f arbitrary >>= evaluate

symbolic :: Monad m => Symbolic a -> Prog m a
symbolic (Symbolic f) = Prog (gets f)

run :: Monad m => m a -> Prog m a
run = Prog . lift

cps :: Monad m => Prog m () -> (Prog m () -> Prog m ())
cps x = \k -> x >> k

queuesM = describe "queuesM" [
 (con "X" X) { typ = TVar },
 (con "Y" Y) { typ = TVar },
 (con "Z" Z) { typ = TVar },
 var "x" (undefined :: Symbolic Elem),
 var "y" (undefined :: Symbolic Elem),
 var "z" (undefined :: Symbolic Elem),
 -- var "x" (undefined :: Symbolic Bool),
 -- var "y" (undefined :: Symbolic Bool),
 -- var "z" (undefined :: Symbolic Bool),
 -- con "read" readB,
 con "read" (read :: Var -> Symbolic Elem),
 -- con "return" (return :: Bool -> QueueProg Bool),
 con "return" (\x v -> symbolic (x :: Symbolic Elem) >>= write v :: Prog QueueM ()),
 var "k" (undefined :: Prog QueueM ()),
 con "empty" ((cps $ run newM)),
 con "isnotempty" (cps $ run (do Queue xs ys <- get; (_:_) <- return (xs++ys); return () :: QueueM ())),
 -- con "null" (\v -> cps $ run nullM >>= writeB v),
 -- con "inl" (\x -> cps $ symbolic x >>= run . inlM),
 con "add" (\x -> cps $ symbolic x >>= run . inrM),
 con "remove" (cps $ run outlM),
 -- con "outr" (cps $ run outrM),
 con "front" (\v -> cps $ run peeklM >>= write v) ]
 -- con "peekr" (\v -> cps $ run peekrM >>= writeV v) ]

noRebinding :: Term Symbol -> Bool
noRebinding t = evalStateT (check t) [] /= Nothing
  where check (Var v) | symbolType v == typeOf X = do
          s <- get
          guard (v `notElem` s)
          put (v:s)
        check (Var v) = return ()
        check (Const _) = return ()
        check (App (Const f) (Var v)) | name f == "read" =
          modify (\s -> if v `elem` s then s else v:s)
        check (App f x) = check f >> check x

allTerms reps n _ _ | n < 0 = error "oops"
allTerms reps 0 ctx _ = []
allTerms reps n ctx ty = syms ctx ty ++
                         [ App f x
                         | ty' <- argTypes ctx ty
                         , x  <- allTerms reps (n-1) ctx ty'
                         , not (termIsUndefined x)
                         , f  <- allTerms reps n ctx (mkFunTy ty' ty)
                         , f `elem` reps
                         , x `elem` reps
                         , not (termIsUndefined f)
                         ]

allTerms' reps n _ _ | n < 0 = error "oops"
allTerms' reps 0 ctx _ = []
allTerms' reps n ctx ty = syms ctx ty ++
                          [ App f x
                          | ty' <- argTypes ctx ty
                          , x <- allTerms' reps (n-1) ctx ty'
                          , not (termIsUndefined x)
                          , f  <- allTerms' reps (n-size x) ctx (mkFunTy ty' ty)
                          , not (termIsUndefined f)
                          , f `elem` reps
                          , x `elem` reps
                          ]

syms ctx ty = [ sym elt
              | elt <- ctx
              , symbolType elt == ty
              , let sym = case typ elt of
                            TVar -> Var
                            TConst -> Const
              ]

count f n d ctx = (length xs, length ys)
  where (xs, ys) = Data.List.partition p (concat [ f n ctx ty | ty <- allTypes ctx ])
        p x = depth x <= d
{-
main = do
  let example = base ++ lists
  cs <- genSeeds >>= tests 3 (zipWith relabel [0..] example)
  let reps = map head (unpack cs)
  print (count (allTerms reps) 3 3 (zipWith relabel [0..] example))
  print (count (allTerms' reps) 7 4 (zipWith relabel [0..] example))-}
