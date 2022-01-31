{-# LANGUAGE BlockArguments #-}

module FunctorialAlgebras.State where

import FunctorialAlgebras (EndoAlgebra (..), Prog, call, handleE, scoped)
import StateC (StateC (..))

data State s x = Get (s -> x) | Put s x
  deriving stock (Functor)

data Local s x = Local s x
  deriving stock (Functor)

get :: forall s scopes. Functor scopes => Prog (State s) scopes s
get = call (Get pure)

put :: Functor scopes => s -> Prog (State s) scopes ()
put s = call (Put s (pure ()))

modify :: Functor scopes => (t -> t) -> Prog (State t) scopes ()
modify f = do
  s <- get
  put (f s)

local :: Functor algs => s -> Prog algs (Local s) x -> Prog algs (Local s) x
local s prog = scoped (Local s prog)

restoring :: Prog (State s) (Local s) b -> Prog (State s) (Local s) b
restoring prog = do
  s <- get
  local s prog

handleState :: forall s x. s -> Prog (State s) (Local s) x -> (s, x)
handleState initialState prog =
  runStateC
    (handleE @_ @_ @(StateC s) EndoAlgebra{pureE, callE, enterE} prog)
    initialState
 where
  pureE = pure
  callE :: State s (StateC s a) -> StateC s a
  callE = \case
    Get k -> getState >>= k
    Put s k -> putState s >> k
  enterE = \case
    Local localState prog -> do
      prevState <- getState
      putState localState
      k <- prog
      putState prevState
      k
  getState = StateC (\s -> (s, s))
  putState s = StateC (\_ -> (s, ()))

a :: Integer -> (Integer, Integer)
a = flip handleState do
  modify (+ (1 :: Integer))
  modify (* 3)
  x <- restoring do
    modify (* 2)
    modify (+ 7)
    get
  pure x
