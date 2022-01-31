{-# LANGUAGE BlockArguments #-}

module FunctorialAlgebras.ParallelComposition where

import Control.Monad (ap, join, void)
import Data.Functor ((<&>))
import FunctorialAlgebras (BaseAlgebra (..), EndoAlgebra (..), Prog, call, handle, scoped)
import Prelude hiding (last)

data State s x
  = Swap (s -> s) ((s, s) -> x)
  deriving stock (Functor)

swap :: Functor scopes => (t -> t) -> Prog (State t) scopes (t, t)
swap f = call (Swap f pure)

get :: forall s scopes. Functor scopes => Prog (State s) scopes s
get = fst <$> swap id

put :: Functor scopes => s -> Prog (State s) scopes ()
put s = void $ swap (const s)

modify :: Functor scopes => (t -> t) -> Prog (State t) scopes ()
modify f = do
  s <- get
  put (f s)

data Parallel x where
  Race :: x -> x -> Parallel x
  Last :: x -> x -> Parallel x
  deriving stock (Functor)

raceP ::
  Functor algs =>
  Prog algs Parallel x ->
  Prog algs Parallel x ->
  Prog algs Parallel (Either x x)
raceP progA progB = scoped (Race (fmap Left progA) (fmap Right progB))

lastP ::
  Functor algs =>
  Prog algs Parallel x ->
  Prog algs Parallel x ->
  Prog algs Parallel (Either x x)
lastP progA progB = scoped (Last (fmap Left progA) (fmap Right progB))

prog ::
  ( forall x.
    Prog (State [Integer]) Parallel x ->
    Prog (State [Integer]) Parallel x ->
    Prog (State [Integer]) Parallel (Either x x)
  ) ->
  Prog (State [Integer]) Parallel Char
prog parallel = do
  modify (2 :)
  p <- parallel
    do
      void $ swap (3 :)
      void $ swap (1 :)
      pure 'a'
    do
      void $ swap (4 :)
      pure 'b'
  pure (either id id p)

handleSR :: forall s x. s -> Prog (State s) Parallel x -> (s, x)
handleSR initialState prog =
  runStateC
    (handle ealg balg pure prog)
    initialState
 where
  ealg :: EndoAlgebra (State s) Parallel (Resumption (StateC s))
  ealg =
    EndoAlgebra
      { pureE = pure
      , callE = \case
          Swap f k -> liftR (swapState f) >>= k
      , enterE = \case
          Race progA progB -> join $ raceR progA progB
          Last progA progB -> join $ lastR progA progB
      }
  balg :: BaseAlgebra (State s) Parallel (Resumption (StateC s)) (StateC s x)
  balg =
    BaseAlgebra
      { callB = \case
          Swap f k -> swapState f >>= k
      , enterB = \case
          Race progA progB -> join $ runResumption (raceR progA progB)
          Last progA progB -> join $ runResumption (lastR progA progB)
      }
  swapState f = StateC (\(!s) -> let !s' = f s in (s', (s, s')))

-- Resumption

data Resumption m a
  = Done a
  | More (m (Resumption m a))
  deriving stock (Functor)

runResumption :: Monad m => Resumption m a -> m a
runResumption (Done a) = pure a
runResumption (More mA) = runResumption =<< mA

raceR :: Monad m => Resumption m a -> Resumption m a -> Resumption m a
raceR r1 r2 = case r1 of
  Done a1 -> Done a1
  More m1 -> case r2 of
    Done a2 -> Done a2
    More m2 -> More do
      rr1 <- m1
      rr2 <- m2
      pure $ raceR rr1 rr2

lastR :: Monad m => Resumption m a -> Resumption m a -> Resumption m a
lastR r1 r2 = case r1 of
  Done _ -> r2
  More m1 -> case r2 of
    Done _ -> r1
    More m2 -> More do
      rr1 <- m1
      rr2 <- m2
      pure $ lastR rr1 rr2

bothR :: Monad m => Resumption m a -> Resumption m a -> Resumption m (a, a)
bothR r1 r2 = case r1 of
  Done a1 -> (a1,) <$> r2
  More m1 -> case r2 of
    Done a2 -> r1 <&> (,a2)
    More m2 -> More do
      rr1 <- m1
      rr2 <- m2
      pure $ bothR rr1 rr2

instance Monad m => Applicative (Resumption m) where
  pure a = Done a
  rF <*> rA = case rF of
    Done f -> case rA of
      Done a -> Done (f a)
      More mA -> More (fmap (fmap f) mA)
    More mF -> case rA of
      Done a -> More (fmap (fmap ($ a)) mF)
      More mA -> More do
        rrF <- mF
        rrA <- mA
        pure $ rrF <*> rrA

instance Monad m => Monad (Resumption m) where
  rA >>= k = case rA of
    Done a -> k a
    More mA -> More do
      rrA <- mA
      pure $ rrA >>= k

liftR :: Functor m => m a -> Resumption m a
liftR mA = More (Done <$> mA)

-- StateC

newtype StateC s a = StateC {runStateC :: s -> (s, a)}
  deriving stock (Functor)

instance Applicative (StateC s) where
  pure a = StateC (\s -> (s, a))
  (<*>) = ap

instance Monad (StateC s) where
  stateA >>= k = StateC $ \s ->
    let !(!s1, !a) = runStateC stateA s
     in runStateC (k a) s1
