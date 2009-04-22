{-# LANGUAGE FlexibleInstances #-}
module Term where

import Data.Ord
import Data.Char
import Data.List

data Symbol
  = Symbol { name :: String, label :: Int, typ :: Type, what :: Maybe Data }

isCon, isVar :: Symbol -> Bool
isCon s = case what s of
            Nothing -> False
            _ -> True
isVar = not . isCon

instance Show Symbol where
    show = name

instance Eq Symbol where
    e1 == e2 = label e1 == label e2

instance Ord Symbol where
    compare = comparing label

relabel :: Int -> Symbol -> Symbol
relabel l e = e { label = l }

isOp :: Symbol -> Bool
isOp s | isCon s && name s == "[]" = False
isOp s | isCon s = not (all isAlpha (name s))
isOp _            = False

data Term c
  = Const c
  | Var Symbol
  | App (Term c) (Term c)
 deriving (Eq)

class Typed a where
    typeOf :: a -> Type

instance Typed Symbol where typeOf = typ

instance Typed c => Typed (Term c) where
    typeOf (Const c) = typeOf c
    typeOf (Var v) = typ v
    typeOf (App t u) = a
        where _ :-> a = typeOf t

flattenTerm :: Term Symbol -> [Maybe Symbol]
flattenTerm (Var s) = [Just s]
flattenTerm (Const s) = [Just s]
flattenTerm (App t u) = [Nothing] ++ flattenTerm t ++ flattenTerm u

depth, size, numVars :: Term c -> Int
depth (App s t) = depth s `max` (1 + depth t)
depth _ = 1

size (App s t) = size s + size t
size _ = 1

numVars (Var _) = 1
numVars (Const _)       = 0
numVars (App s t)     = numVars s + numVars t

vars :: Term c -> [Symbol]
vars (App s t) = nub (vars s ++ vars t)
vars (Var s)   = [s]
vars _         = []

instance Ord (Term Symbol) where
  s `compare` t = stamp s `compare` stamp t
   where
    stamp t = (depth t, size t, -occur t, top t, args t)
    
    occur t = length (vars t)
    
    top (Var s)   = Just s
    top (Const s) = Just s
    top _         = Nothing
    
    args (App s t) = [s,t]
    args _         = []

instance Show (Term Symbol) where
  showsPrec _ (Const s)   | isOp s    = showString ("(" ++ show s ++ ")")
                          | otherwise = shows s
  showsPrec _ (Var s) = shows s
  showsPrec p (App f x)             = showString (showApp p f [x])
   where
     paren 0 s = s
     paren _ s = "(" ++ s ++ ")"
   
     showApp p (App f x) xs =
       showApp p f (x:xs)
     
     showApp p (Const op) [x] | isOp op =
       paren 9 (show' x ++ show op)

     showApp p (Const op) [x,y] | isOp op =
       paren p (show' x ++ show op ++ show' y)

     showApp p f xs =
       paren p (concat (intersperse " " (map show' (f:xs))))

show' :: Show a => a -> String
show' x = showsPrec 1 x ""

infixr 4 :->

data Type
  = Simple String
  | TCon String Type
  | Type :-> Type
 deriving (Eq, Ord)

instance Show Type where
  showsPrec _ (Simple s)      = showString s
  showsPrec _ (TCon "[]" t)   = showString "[" . showsPrec 0 t . showString "]"
  showsPrec p (TCon c t)      = paren (p>=2) (showString c . showString " " . showsPrec 2 t)
  showsPrec p (s :-> t)       = paren (p>=1) (showsPrec 1 s . showString " -> " . showsPrec 0 t)

paren False s = s
paren True s = showString "(" . s . showString ")"

data Data
  = Int Int
  | Bool Bool
  | List [Data]
  | Fun (Data -> Data)

instance Eq Data where
  x == y = x `compare` y == EQ

instance Ord Data where
  Int n1  `compare` Int n2  = n1 `compare` n2
  Bool b1 `compare` Bool b2 = b1 `compare` b2
  List xs `compare` List ys = xs `compare` ys
  Fun _   `compare` Fun _   = error "no instance Ord (Fun _)"
  _       `compare` _       = error "no instance Ord for different types"
