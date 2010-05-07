{-# LANGUAGE TemplateHaskell #-}

-- Template Haskell magic.
-- Can be used in place of "con" for polymorphic functions.

module Monomorphise where

import Debug.Trace
import Language.Haskell.TH
import Term

traceIt x = trace (show x) x
traceTy x = trace (show (pprint x)) x

infoName :: Info -> Name
infoName (ClassOpI name _ _ _) = name
infoName (DataConI name _ _ _) = name
infoName (VarI name _ _ _) = name

infoType :: Info -> Type
infoType (ClassOpI _ ty _ _) = ty
infoType (DataConI _ ty _ _) = ty
infoType (VarI _ ty _ _) = ty

monomorphiseType :: Type -> Type -> Type
monomorphiseType poly (ForallT xs ctx ty) = inner ty
  where inner (ForallT _ _ _) = error "don't know how to monomorphise higher-ranked types"
        inner (VarT n) | n `elem` xs = poly
        inner (AppT t1 t2) = AppT (inner t1) (inner t2)
        inner t = t

monomorphise :: Name -> Q Exp
monomorphise t = do
  ty <- fmap infoType (reify t)
  int <- [t| Int |]
  let ty' = monomorphiseType int ty
  return (SigE (VarE t) ty')

con' :: Name -> Q Exp
con' t = do
  name <- fmap (nameBase . infoName) (reify t)
  [| con name $(monomorphise t) |]

con'' :: Q Exp -> Q Exp
con'' t = do
  name <- fmap (nameBase . expName) t
  [| con name $t |]

var' :: String -> Q Type -> Q Exp
var' name ty = do
  ty' <- ty
  undef <- [| undefined |]
  [| var name $(return (SigE undef ty')) |]

expName :: Exp -> Name
expName (VarE x) = x
expName (ConE x) = x
expName (SigE e _) = expName e
expName e = error $ "unknown name " ++ show e