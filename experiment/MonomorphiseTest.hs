{-# LANGUAGE TemplateHaskell #-}

module Main where

import Monomorphise

f x = x
g x = x+1
h x = x == x

f' = $(monomorphise 'f)
g' = $(monomorphise 'g)
--h' = $(monomorphise 'h)

sym = $(con' 'g)