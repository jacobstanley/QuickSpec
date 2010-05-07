module Experiment where

import Control.Monad

data Term = App Term Term | Const String | Var String deriving Show
data Type = TyConst String | TyFun Type Type deriving (Eq, Show)

tyFun :: [Type] -> Type -> Type
tyFun [] ty = ty
tyFun (ty:tys) ty' = TyFun ty (tyFun tys ty')

bool = TyConst "Bool"

type Context = [(Term, Type)]

ctx = [(Const "&&", tyFun [bool, bool] bool),
       (Const "not", tyFun [bool] bool),
       (Const "true", bool),
       (Var "x", bool),
       (Var "y", bool)]

types :: Context -> [Type]
types ctx = concatMap (closure . snd) ctx
  where closure ty@(TyFun ty1 ty2) = ty:closure ty2
        closure ty = [ty]

-- gen :: Int -> Context -> Type -> Term -> [Term]
-- gen 0 ctx ty shape = [ t | (t, ty') <- ctx, ty == ty', t `matches` shape ]
-- gen (n+1) ctx ty shape = gen 0 ctx ty shape ++
--                          [ App f x | TyFun ty1 ty2 <- types ctx,
--                                      ty2 == ty,
--                                      (l, r) <- split shape,
--                                      f <- gen (n+1) ctx (TyFun ty1 ty2) l,
--                                      x <- gen n ctx ty1 r ]

-- what about the depth optimisation?
-- maybe---not Constraint = Term -> Bool, but type :: Term -> Constraint.
-- Then we can keep a map Constraint -> Set Term.
-- Downwards information flow:
--   to generate a term of size 6, generate terms of size 5 and 1 or 4 and 2 or ...
--   where these two subterms are equal
-- (how about: find out which hole has fewest possible instantiations,
-- brute-force try all of them)
-- constraint intersections would work fine!
-- app :: Constraint -> [(Constraint, Constraint)] for generating apps
-- But what about depth optimisation???????
-- Ah, maybe it's enough to have a postfiltering phase.

data Constraint = Constraint { depth :: Int, size :: Int, typ :: Maybe Type }

gen :: Context -> [Constraint] -> [Term]
gen ctx cs = [ t | (t, ty) <- ctx, any (contextSatisfies t ty) cs ] ++
              [ App f x | c <- cs,
                          (c1, c2) <- split c,
                          f <- gen ctx cst1,
                          x <- gen ctx cst2 ]

contextSatisfies t ty cst = typ cst == Just ty && size cst == 1

split (Constraint _ _ Nothing) = []
split (Constraint m n _) | m <= 0 || n <= 0 = []
split (Constraint d s (Just ty)) =
  [ (Constraint d s1 (Just (TyFun ty1 ty)),
     Constraint (d-1) s2 (Just ty1))
  | TyFun ty1 ty2 <- types ctx,
    ty == ty2,
    s1 <- [1..s-1],
    let s2 = s-s1
  ]
