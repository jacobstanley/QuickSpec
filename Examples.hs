{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Equations
import Term
import Data.List(insert)

boolVars = [
 var "x" False,
 var "y" False,
 var "z" False
 ]

boolCons = [
 con "&&" (&&),
 con "||" (||),
 con "not" not,
 con "true" True,
 con "false" False
 ]

baseVars = [
 var "x" int,
 var "y" int,
 var "z" int ]
  where int :: Int
        int = undefined

listVars = [
 var "xs" list,
 var "ys" list,
 var "zs" list ]
  where list :: [Int]
        list = undefined

listCons = [
 con "++" ((++) :: [Int] -> [Int] -> [Int]),
 con "reverse" (reverse :: [Int] -> [Int]),
 con "tail" (tail :: [Int] -> [Int]),
 con ":" ((:) :: Int -> [Int] -> [Int]),
 con "[]" ([] :: [Int]),
 con "unit" (\x -> [x] :: [Int]),
 con "insert" (insert :: Int -> [Int] -> [Int])]

main = laws (boolVars ++ boolCons) 3