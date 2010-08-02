{-# LANGUAGE GeneralizedNewtypeDeriving,DeriveDataTypeable #-}
module Regex where

import Debug.Trace
import qualified Control.Monad.State as S
import Control.Monad.State hiding (State)
import qualified Data.Map as M
import Data.List
import Data.Map(Map)
import Data.Typeable

newtype State = State Int deriving (Eq, Ord, Num, Show)

data NFA a = NFA {
    epsilons :: Map State [State],
    transitions :: Map (State, Maybe a) [State],
    initial :: State,
    final :: State } deriving Show

data Regex a = Char a | AnyChar | Epsilon | Zero
             | Concat (Regex a) (Regex a)
             | Choice (Regex a) (Regex a)
             | Plus (Regex a) deriving (Typeable, Show)

star r = Choice Epsilon (Plus r)

type M a = S.State ([(State, Maybe a, State)], [(State, State)], State)

edge :: State -> Maybe a -> State -> M a ()
edge start e end = modify (\(edges, epsilons, next) -> ((start, e, end):edges, epsilons, next))

epsilon :: State -> State -> M a ()
epsilon start end = modify (\(edges, epsilons, next) -> (edges, (start, end):epsilons, next))

state :: M a State
state = do
  (edges, epsilons, next) <- get
  put (edges, epsilons, next+1)
  return next

compile1 :: Regex a -> State -> State -> M a ()
compile1 (Char c) start end = edge start (Just c) end
compile1 AnyChar start end = edge start Nothing end
compile1 Zero start end = return ()
compile1 Epsilon start end = epsilon start end
compile1 (Concat r s) start end = do
  mid <- state
  compile1 r start mid
  compile1 s mid end
compile1 (Choice r s) start end = do
  compile1 r start end
  compile1 s start end
compile1 (Plus r) start end = do
  start' <- state
  end' <- state
  epsilon start start'
  epsilon end' end
  epsilon end' start'
  compile1 r start' end'

compile :: (Show a, Ord a) => Regex a -> NFA a
compile r = NFA (close (foldr enter M.empty epsilons)) (foldr flatten M.empty edges) (State 0) (State 1)
  where (edges, epsilons, _) = execState (compile1 r (State 0) (State 1)) ([], [], State 2)
        flatten (start, edge, to) edges = M.insertWith (++) (start, edge) [to] edges
        enter (from, to) epsilons = M.insertWith (++) from [to] epsilons

close :: (Show a, Ord a) => Map a [a] -> Map a [a]
close m | xs == [] = m
        | otherwise = close (foldr enter m xs)
        where enter (from, to) epsilons = M.insertWith (++) from [to] epsilons
              xs = nub' (close1 m)

close1 m = do
  (from, tos) <- M.toList m
  to <- tos
  to' <- M.findWithDefault [] to m
  guard (to' `notElem` tos && to' /= to && to' /= from)
  return (from, to')

run :: Ord a => NFA a -> [a] -> Bool
run nfa = runFrom nfa [initial nfa]
runFrom nfa states = runFrom' nfa (nub' (concatMap (epsilonClosed nfa) states))
runFrom' nfa states [] = final nfa `elem` states
runFrom' nfa states (x:xs) = runFrom nfa (nub' $ concat [ M.findWithDefault [] (s, Just x) (transitions nfa) ++ M.findWithDefault [] (s, Nothing) (transitions nfa) | s <- states ]) xs
epsilonClosed nfa s = s:M.findWithDefault [] s (epsilons nfa)

nub' :: Ord a => [a] -> [a]
nub' = map head . group . sort