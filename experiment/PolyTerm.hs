data PolyTerm where

data Map a b = Map ((a -> b) -> [a] -> [b])

instance (Classify a, Classify b) => Classify (Map a b) where
  -- ...

