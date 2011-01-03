{-# LANGUAGE GeneralizedNewtypeDeriving, DoRec, ExistentialQuantification, FlexibleContexts #-}
module TermSet2 where

import Control.Arrow((***))
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.IntMap as IntMap
import Data.IntMap(IntMap)
import Test.QuickCheck hiding (label)
import Test.QuickCheck.Gen
import Test.QuickCheck.GenT hiding (liftGen)
import qualified Test.QuickCheck.GenT as GenT
import Data.Typeable
import TestTree

newtype Label v a = Label { unLabel :: State (Int, IntMap v) a } deriving (Functor, Monad, MonadFix)

label :: v -> Label v (Labelled v)
label x = Label $ do
  (i, m) <- get
  put (i+1, IntMap.insert i x m)
  return (Labelled i x)

data Labelled a = Labelled Int a

runLabel :: Label v a -> (a, IntMap v)
runLabel = (id *** snd) . flip runState (0, IntMap.empty) . unLabel

-- test :: Assoc Int ()
-- test = do
--   rec x <- assoc y
--       y <- assoc x
--   return ()

data UntypedTestResults = forall a. Typeable a => UntypedTestResults (TestResults a)

newtype Univ a = Univ { unUniv :: ReaderT Int (GenT (Label UntypedTestResults)) a }
  deriving (Functor, Monad, MonadFix, MonadReader Int)

testCases :: Gen a -> Gen [a]
testCases g = forM (cycle [1..50]) $ \n -> resize n g

generate :: Typeable a => TestTree a -> Univ (Labelled a)
generate t = do
  n <- ask
  liftLabel (label (UntypedTestResults (cutOff n t)))

liftGen :: Gen a -> Univ a
liftGen = Univ . lift . GenT.liftGen

liftLabel :: Label UntypedTestResults a -> Univ a
liftLabel = Univ . lift . lift

base :: (Ord a, Eval a, Typeable a, Arbitrary (TestCase a)) => [a] -> Univ (Labelled a)
base ts = do
  tcs <- liftGen (testCases arbitrary)
  generate (test tcs ts)

apply :: Labelled (a -> b) -> Labelled a -> Univ (Labelled b)
apply fs xs = do
  tcs <- liftGen (testCases arbitrary)
  undefined
--  generate (test tcs (
