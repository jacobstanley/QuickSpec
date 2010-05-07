newtype Diag a = MkDiag { unDiag :: [a] } deriving Show
instance Monad Diag where
  return x = MkDiag [x]
  MkDiag xs >>= f = MkDiag (concat (diag (map (unDiag . f) xs)))

diag [] = []
diag (xs:xss) = zipWith (++) [ [x] | x <- xs ] ([] : diag xss)