{-# LANGUAGE TypeFamilies,GeneralizedNewtypeDeriving,DeriveDataTypeable #-}
module PrettyPrinting where

import Term
import Data.List
import Data.Typeable
import Test.QuickCheck
import Control.Monad

newtype Layout = Layout [(Int, String)] deriving (Typeable, Eq, Ord, Show)

instance Arbitrary Layout where
  arbitrary = fmap Layout (liftM2 (:) arbitrary arbitrary)

instance Classify Layout where
  type Value Layout = Layout
  evaluate = return

text :: String -> Layout
text s = Layout [(0, s)]

nest :: Int -> Layout -> Layout
nest k (Layout l) = Layout [(i+k, s) | (i, s) <- l]

($$) :: Layout -> Layout -> Layout
Layout xs $$ Layout ys = Layout (xs ++ ys)

(<>) :: Layout -> Layout -> Layout
Layout xs <> Layout ys = f (init xs) (last xs) (head ys) (tail ys)
  where f xs (i, s) (j, t) ys = Layout xs $$ Layout [(i, s ++ t)] $$ nest (i + length s - j) (Layout ys)

pretty = describe "pretty" [
          var "d" (text ""),
          var "e" (text ""),
          var "f" (text ""),
          con "text" text,
          con "nest" nest,
          con "$$" ($$),
          con "<>" (<>)]
         ++ [
          var "s" "",
          var "t" "",
          var "u" "",
          con "\"\"" "",
          con "++" ((++) :: String -> String -> String)]

instance Classify Char where
  type Value Char = Char
  evaluate = return
