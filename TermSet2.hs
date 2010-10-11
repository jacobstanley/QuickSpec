{-# LANGUAGE GeneralizedNewtypeDeriving, DoRec, ExistentialQuantification #-}
module TermSet2 where

import Control.Arrow((***))
import Control.Monad.State
import qualified Data.IntMap as IntMap
import Data.IntMap(IntMap)
import Test.QuickCheck
import Data.Typeable
import TestTree

newtype Assoc v a = Assoc { unAssoc :: State (Int, IntMap v) a } deriving (Functor, Monad, MonadFix)

assoc :: v -> Assoc v Int
assoc x = Assoc $ do
  (i, m) <- get
  put (i+1, IntMap.insert i x m)
  return i

runAssoc :: Assoc v a -> (a, IntMap v)
runAssoc = (id *** snd) . flip runState (0, IntMap.empty) . unAssoc

-- test :: Assoc Int ()
-- test = do
--   rec x <- assoc y
--       y <- assoc x
--   return ()

data UntypedTestResults = forall a. Typeable a => UntypedTestResults (TestResults a)

newtype Univ a = Univ { unUniv :: Int -> Gen (Assoc UntypedTestResults a) }
newtype Label a = Label Int

testCases :: Arbitrary a => Gen [a]
testCases = forM (cycle [1..50]) $ \n -> resize n arbitrary

generate :: Typeable a => TestTree a -> Univ (Label a)
generate t = Univ $ \n -> return (fmap Label (assoc (UntypedTestResults (cutOff n t))))

