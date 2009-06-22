{-# LANGUAGE GADTs,TypeFamilies,FlexibleInstances,FlexibleContexts,DeriveDataTypeable,ScopedTypeVariables #-}
module Term where

import Data.Ord
import Data.Char
import Data.List
import Data.Maybe
import Data.Typeable
import System.Random
import Test.QuickCheck hiding (label)
import Test.QuickCheck.Gen

-- Terms.

data Symbol
  = Symbol { name :: String, label :: Int, isVar :: Bool, range :: Gen Data }
  deriving Typeable

instance Show Symbol where
  show = name

instance Eq Symbol where
  e1 == e2 = label e1 == label e2

instance Ord Symbol where
  compare = comparing label

relabel :: Int -> Symbol -> Symbol
relabel l e = e { label = l }

isCon :: Symbol -> Bool
isCon = not . isVar

isOp :: Symbol -> Bool
isOp s | isCon s && name s == "[]" = False
isOp s | isCon s = not (all isAlphaNum (name s))
isOp _ = False

var :: forall a. (Classify a, Arbitrary a) => String -> a -> Symbol
var name _ = Symbol { name = name, label = undefined, isVar = True, range = fmap Data (arbitrary :: Gen a) }

con :: Classify a => String -> a -> Symbol
con name impl = Symbol { name = name, label = undefined, isVar = False, range = fmap Data (return impl) }

data Term c = Const c | Var Symbol | App (Term c) (Term c) deriving (Typeable, Eq)

depth, size, numVars :: Term c -> Int
depth (App s t) = depth s `max` (1 + depth t)
depth _ = 1

size (App s t) = size s + size t
size _ = 1

numVars (Var _) = 1
numVars (Const _) = 0
numVars (App s t) = numVars s + numVars t

vars :: Term c -> [Symbol]
vars (App s t) = nub (vars s ++ vars t)
vars (Var s)   = [s]
vars _         = []

mapVars :: (Symbol -> Symbol) -> Term c -> Term c
mapVars f (Const k) = Const k
mapVars f (Var v)   = Var (f v)
mapVars f (App t u) = App (mapVars f t) (mapVars f u)

instance Ord s => Ord (Term s) where
  s `compare` t = stamp s `compare` stamp t
   where
    stamp t = (depth t, size t, -occur t, top t, args t)
    
    occur t = length (vars t)
    
    top (Var s)   = Just (Left s)
    top (Const s) = Just (Right s)
    top _         = Nothing
    
    args (App s t) = [s, t]
    args _         = []

instance Show (Term Symbol) where
  showsPrec _ (Const s)   | isOp s    = showString ("(" ++ show s ++ ")")
                          | otherwise = shows s
  showsPrec _ (Var s)   = shows s
  showsPrec p (App f x) = showString (showApp p f [x])
   where
     paren 0 s = s
     paren _ s = "(" ++ s ++ ")"
   
     showApp p (App f x) xs =
       showApp p f (x:xs)
     
     showApp p (Const op) [x] | isOp op =
       paren 9 (show' x ++ show op)

     showApp p (Const op) [x,y] | isOp op =
       paren p (show' x ++ show op ++ show' y)

     showApp p (Const op) (x:y:xs) | isOp op =
       paren p (concat (intersperse " " (paren 9 (show' x ++ show op ++ show' y):map show' xs)))

     showApp p f xs =
       paren p (concat (intersperse " " (map show' (f:xs))))

     show' x = showsPrec 1 x ""

-- Types.

funTypes :: [TypeRep] -> [(TypeRep, TypeRep)]
funTypes tys =
  [ (ty1, ty2) | ty <- tys,
                 (c, [ty1, ty2]) <- [splitTyConApp ty],
                 tyConString c == "->" ]

symbolType :: Symbol -> TypeRep
symbolType s =
  case unGen evalSym undefined undefined s of
    Data x -> typeOf x

termType :: Term Symbol -> TypeRep
termType (Var s) = symbolType s
termType (Const s) = symbolType s
termType (App t u) = fromJust (funResultTy (termType t) (termType u))

resultTypes :: TypeRep -> [TypeRep]
resultTypes ty = ty:concat [ resultTypes ty' | (_, ty') <- funTypes [ty] ]

allTypes :: [Symbol] -> [TypeRep]
allTypes ctx = nub (concatMap (resultTypes . symbolType) ctx)

-- Evaluation.

data Data where
  Data :: Classify a => a -> Data

evalSym :: Gen (Symbol -> Data)
evalSym = promote (\s -> label s `coarbitrary` range s)

eval :: (Symbol -> Data) -> Term Symbol -> Data
eval ctx (Const s) = ctx s
eval ctx (Var s) = ctx s
eval ctx (App t u) =
  case (eval ctx t, eval ctx u) of
    (Data v, Data w) -> apply v w

class (Typeable a, Ord (Value a), Typeable (Value a)) => Classify a where
  type Value a
  evaluate :: a -> Gen (Value a)
  apply :: Typeable b => a -> b -> Data
  apply = error "ill-typed term formed"

instance (Typeable a, Arbitrary a, Classify b) => Classify (a -> b) where
  type Value (a -> b) = Value b
  evaluate f = do
    x <- arbitrary
    evaluate (f x)
  apply f x =
    case cast x of
      Just x' -> Data (f x')
      Nothing -> error "ill-typed term formed"

instance Classify Bool where
  type Value Bool = Bool
  evaluate = return

instance Classify Int where
  type Value Int = Int
  evaluate = return

instance Classify a => Classify [a] where
  type Value [a] = [Value a]
  evaluate = mapM evaluate

data AnyValue where
  Value :: (Typeable a, Ord a) => a -> AnyValue
instance Eq AnyValue where
  x == y = x `compare` y == EQ
instance Ord AnyValue where
  Value x `compare` Value y =
    case cast x of
      Just x' -> x' `compare` y
      Nothing -> error "incomparable"

evalWithSeed :: (StdGen, Int) -> Term Symbol -> AnyValue
evalWithSeed (rnd, n) s = unGen testM rnd n
  where testM = do
          evalSym' <- evalSym
          case eval evalSym' s of
            Data x -> fmap Value (evaluate x)