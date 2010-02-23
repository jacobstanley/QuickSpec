{-# LANGUAGE ScopedTypeVariables,EmptyDataDecls,TypeFamilies,DeriveDataTypeable #-}
import Codec.TPTP.Base hiding (formula, Var, Formula, Term)
import qualified Codec.TPTP.Base as TPTP
import Codec.TPTP.Import
import Control.Arrow hiding (left, right)
import Control.Monad
import Control.Monad.Identity
import Data.List hiding (find)
import Data.Maybe
import Data.Monoid hiding (All)
import Data.Typeable
import System
import System.IO
import Test.QuickCheck
import qualified Term
import Equations hiding (prune)
import CongruenceClosure

-- Parsing

relativeTo :: FilePath -> FilePath -> FilePath
relativeTo dir file = dir ++ "/" ++ file

inProblemDir :: FilePath -> FilePath
inProblemDir name = "Problems/" ++ take 3 name ++ "/" ++ name ++ ".p"

verbose :: (FilePath -> IO a) -> FilePath -> IO a
verbose f file = do
  putStr ("Parsing " ++ file ++ "... ")
  result <- f file
  putStrLn "OK!"
  return result

parseProblem :: FilePath -> FilePath -> IO [TPTP_Input]
parseProblem dir = verbose (fmap checkKind . parseWithIncludes dir) . relativeTo dir . inProblemDir

parseWithIncludes :: FilePath -> FilePath -> IO [TPTP_Input]
parseWithIncludes dir file = parseFile file >>= fmap concat . mapM parseIncludes
  where parseIncludes (Include file []) = parseWithIncludes dir (relativeTo dir file)
        parseIncludes (Include file _) = error "strange include directive"
        parseIncludes x = return [x]

-- Problem representation

data Problem = Problem { axioms :: [Formula], conjectures :: [Formula] } deriving Show
data Formula = Formula { vars :: [String], left :: Term, right :: Term } deriving Show
data Term = Var String | App String [Term] deriving Show

instance Monoid Problem where
  mempty = Problem [] []
  Problem fs gs `mappend` Problem fs' gs' = Problem (fs ++ fs') (gs ++ gs')

formula :: TPTP_Input -> Problem
formula (AFormula _ r f NoAnnotations)
  | unrole r `elem` ["hypothesis", "axiom"] = Problem [convertFormula f] []
  | unrole r == "negated_conjecture" = Problem [] [convertFormula f]
  | otherwise = error ("strange role " ++ unrole r)
formula _ = Problem [] []

convert :: [TPTP_Input] -> Problem
convert xs = mconcat (map formula xs)

checkKind :: [TPTP_Input] -> [TPTP_Input]
checkKind prob | any (== Comment "% Status   : Unsatisfiable") prob = prob
               | otherwise = error "wrong kind of problem"

convertFormula :: TPTP.Formula -> Formula
convertFormula (F (Identity (Quant All vs t))) = Formula (map unV vs) (fst x) (snd x)
  where unV (V x) = x
        x = convertPred t
convertFormula t = Formula [] (fst x) (snd x)
  where x = convertPred t

convertPred :: TPTP.Formula -> (Term, Term)
convertPred (F (Identity (InfixPred t (:=:) u))) = (convertTerm t, convertTerm u)
convertPred (F (Identity (InfixPred t (:!=:) u))) = (convertTerm t, convertTerm u)
convertPred _ = error "strange term"

convertTerm :: TPTP.Term -> Term
convertTerm (T (Identity (FunApp (AtomicWord f) xs))) = App f (map convertTerm xs)
convertTerm (T (Identity (TPTP.Var (V x)))) = Var x
convertTerm _ = error "strange term"

-- Functions on problems, converting terms to QuickSpec terms

formulae :: Problem -> [Formula]
formulae (Problem axioms conjectures) = axioms ++ conjectures

numVars :: Problem -> Int
numVars = maximum . map (length . vars) . formulae

symbols :: Problem -> [(String, Int)]
symbols = usort . concatMap formSyms . formulae
  where formSyms (Formula _ t u) = termSyms t ++ termSyms u
        termSyms (Var _) = []
        termSyms (App f ts) = (f, length ts):concatMap termSyms ts
        usort = map head . group . sort

data Void deriving (Typeable)
instance Eq Void where
  _==_ = undefined
instance Ord Void where
  _<=_ = undefined
instance Arbitrary Void where
  arbitrary = return undefined
instance Term.Classify Void where
  type Term.Value Void = Void
  evaluate = return

range :: Int -> Term.Data
range 0 = Term.Data (undefined :: Void)
range (n+1) = case range n of
                Term.Data x -> Term.Data (\(_ :: Void) -> x)

symbol :: Term.SymbolType -> (String, Int) -> Term.Symbol
symbol typ (name, arity) = Term.Symbol name Nothing undefined False typ (return (range arity))

context :: Problem -> Context
context prob = zipWith Term.relabel [0..] ctx
  where ctx = map (symbol Term.TConst) (symbols prob) ++
              [ symbol Term.TVar (v, 0) | v <- varNames ]
        varNames = head [ vars f | f <- formulae prob, length (vars f) == numVars prob ]

toQuickSpec :: Context -> [String] -> Term -> Term.Term Term.Symbol
toQuickSpec ctx vars (Var v) = Term.Var sym
  where sym = [ s | s <- ctx, Term.typ s == Term.TVar ] !!
                fromJust (elemIndex v vars)
toQuickSpec ctx vars (App f ts) = foldl Term.App (Term.Const sym)
                                            (map (toQuickSpec ctx vars) ts)
  where sym = head [ s | s <- ctx, Term.typ s == Term.TConst,
                     Term.name s == f,
                     arity (Term.symbolType s) == length ts ]

arity :: TypeRep -> Int
arity ty = case Term.funTypes [ty] of
             [] -> 0
             [(_, rhs)] -> 1+arity rhs

-- Term generation and pruning.

load :: Context -> Int -> [Formula] -> [Term.Term Term.Symbol] -> CC ()
load ctx d fs univ = do
  univ' <- loadUniv univ
  forM_ fs $ \f ->
    consequences d univ' [] (convert f (left f), convert f (right f))
      where convert f t = killSymbols (toQuickSpec ctx (vars f) t)

allTerms :: Context -> Int -> Int -> [Formula] -> [Term.Term Term.Symbol]
allTerms _ 0 _ _ = []
allTerms ctx (d+1) d' fs = sort (concat [ terms ctx base ty | ty <- Term.allTypes ctx ])
  where base ty = [ t | t <- pruned, Term.termType t == ty ]
        pruned = prune ctx d' fs (allTerms ctx d d' fs)

prune :: Context -> Int -> [Formula] -> [Term.Term Term.Symbol] -> [Term.Term Term.Symbol]
prune ctx d fs ts = runCC (length ctx) $ do
                      load ctx d fs ts
                      reps <- forM ts $ \x -> flatten (killSymbols x) >>= rep
                      return (takeReps (zip reps ts))
  where takeReps = sort . map (snd . head) . groupBy (equalsOn fst) . sort
        equalsOn f x y = f x == f y

-- Main program

defaultPath = "/home/nick/TPTP-v4.0.1"

problemList :: IO [FilePath]
problemList = fmap words (readFile "ueq-problems")

test :: FilePath -> IO ()
test file = parseProblem defaultPath file >>= print . convert

main = do
  hSetBuffering stdout NoBuffering
  let withDefault _ [x] = x
      withDefault x [] = x
  path <- fmap (withDefault defaultPath) getArgs
  problems <- problemList
  forM problems $ \name -> do
         prob <- fmap (convert . checkKind) (parseProblem path name)
         prob `seq` return prob -- give an error if conversion fails
