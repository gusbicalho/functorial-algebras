{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}

module SplitScopedProg.FunAlg where

import Control.Monad (ap, join, void)
import Data.Kind (Type)
import StateC (StateC (..))

-- Syntax tree for top-level and scoped programs

type Signature = Type -> Type

newtype Prog algs scopes scopedAlgs x = Prog
  { getProg :: Syntax algs scopes (Prog scopedAlgs scopes scopedAlgs) x
  }
  deriving newtype (Functor, Applicative, Monad)

type Syntax :: Signature -> Signature -> Signature -> Type -> Type
data Syntax algs scopes scopedSyntax x where
  Pure :: x -> Syntax algs scopes scopedAlgs x
  Call :: (algs (Syntax algs scopes scopedAlgs x)) -> Syntax algs scopes scopedAlgs x
  Enter :: scopes (scopedSyntax (Syntax algs scopes scopedSyntax x)) -> Syntax algs scopes scopedSyntax x
  deriving stock (Functor)

instance (Functor algs, Functor scopes, Functor scopedAlgs) => Applicative (Syntax algs scopes scopedAlgs) where
  pure = Pure
  (<*>) = ap

instance (Functor algs, Functor scopes, Functor scopedAlgs) => Monad (Syntax algs scopes scopedAlgs) where
  Pure x >>= k = k x
  Call algOp >>= k = Call (fmap (>>= k) algOp)
  Enter innerOp >>= k = Enter ((fmap . fmap) (>>= k) innerOp)

-- Handlers

type EndoAlgebra :: Signature -> Signature -> (Type -> Type) -> Type
data EndoAlgebra algs scopes f = EndoAlgebra
  { pureE :: forall x. x -> f x
  , callE :: forall x. algs (f x) -> f x
  , enterE :: forall x. scopes (f (f x)) -> f x
  }

type BaseAlgebra :: Signature -> Signature -> (Type -> Type) -> Type -> Type
data BaseAlgebra algs scopes f x = BaseAlgebra
  { callB :: algs x -> x
  , enterB :: scopes (f x) -> x
  }

handle ::
  forall algs scopes scopedAlgs f a b.
  (Functor algs, Functor scopes, Functor scopedAlgs, Functor f) =>
  EndoAlgebra scopedAlgs scopes f ->
  BaseAlgebra algs scopes f b ->
  (a -> b) ->
  Prog algs scopes scopedAlgs a ->
  b
handle ealg = handleBase (handleScoped ealg)

handleBase ::
  forall algs scopes scopedAlgs f a b.
  (Functor algs, Functor scopes, Functor f, Functor scopedAlgs) =>
  (forall x. Prog scopedAlgs scopes scopedAlgs x -> f x) ->
  BaseAlgebra algs scopes f b ->
  (a -> b) ->
  Prog algs scopes scopedAlgs a ->
  b
handleBase handleScoped BaseAlgebra{callB, enterB} gen = go . getProg
 where
  go :: Syntax algs scopes (Prog scopedAlgs scopes scopedAlgs) a -> b
  go (Pure a) = gen a
  go (Call algOp) = callB $ fmap go algOp
  go (Enter innerOp) = enterB (fmap (handleScoped . fmap go) innerOp)

handleScoped ::
  forall f x algs scopes.
  (Functor f, Functor algs, Functor scopes) =>
  EndoAlgebra algs scopes f ->
  Prog algs scopes algs x ->
  f x
handleScoped EndoAlgebra{pureE, callE, enterE} = go . getProg
 where
  go :: forall x. Syntax algs scopes (Prog algs scopes algs) x -> f x
  go (Pure a) = pureE a
  go (Call algOp) = callE (fmap go algOp)
  go (Enter scopedOp) = enterE (fmap (go . fmap go . getProg) scopedOp)

handleE ::
  forall algs scopes f x.
  (Functor algs, Functor scopes, Monad f) =>
  EndoAlgebra algs scopes f ->
  Prog algs scopes algs x ->
  f x
handleE ealg@EndoAlgebra{pureE, callE, enterE} =
  handle ealg BaseAlgebra{callB = callE, enterB = enterE} pureE

-- Helpers to lift effect functors into Prog

call ::
  algs (Syntax algs scopes (Prog scopedAlgs scopes scopedAlgs) x) ->
  Prog algs scopes scopedAlgs x
call = Prog . Call

scoped ::
  (Functor scopes, Functor scopedAlgs, Functor algs) =>
  scopes (Prog scopedAlgs scopes scopedAlgs x) ->
  Prog algs scopes scopedAlgs x
scoped = Prog . Enter . fmap (fmap pure)

-- State effect

data State s x = Swap (s -> s) ((s, s) -> x)
  deriving stock (Functor)

data Local s x = Local s x
  deriving stock (Functor)

swap ::
  (Functor scopes, Functor scopedAlgs) =>
  (s -> s) ->
  Prog (State s) scopes scopedAlgs (s, s)
swap f = call (Swap f pure)

modify ::
  (Functor scopes, Functor scopedAlgs) =>
  (s -> s) ->
  Prog (State s) scopes scopedAlgs ()
modify f = void (swap f)

get ::
  (Functor scopes, Functor scopedAlgs) =>
  Prog (State s) scopes scopedAlgs s
get = snd <$> swap id

put :: (Functor scopes, Functor scopedAlgs) => s -> Prog (State s) scopes scopedAlgs ()
put s = void $ swap (const s)

local ::
  (Functor scopedAlgs, Functor algs) =>
  s ->
  Prog scopedAlgs (Local s) scopedAlgs x ->
  Prog algs (Local s) scopedAlgs x
local s prog = scoped (Local s prog)

-- Handle program with global state and local scoping

handleGlobalState :: forall s x. s -> Prog (State s) (Local s) (State s) x -> (s, x)
handleGlobalState initialState prog =
  runStateC
    (handleE @_ @_ @(StateC s) EndoAlgebra{pureE, callE, enterE} prog)
    initialState
 where
  pureE = pure
  callE :: State s (StateC s a) -> StateC s a
  callE = \case
    Swap f k -> swapState f >>= k
  enterE = \case
    Local localState prog -> do
      (prevState, _) <- swapState (const localState)
      k <- prog
      void $ swapState (const prevState)
      k
  swapState f = StateC (\(!s0) -> let !s1 = f s0 in (s1, (s0, s1)))

a :: Integer -> (Integer, Integer)
a = flip handleGlobalState do
  modify (+ (1 :: Integer))
  modify (* 3)
  s <- get
  x <- local s do
    modify (* 2)
    modify (+ 7)
    get
  pure x

-- >>> a 1
-- (6, 19)

-- Handle program with local state only

data Void1 x
  deriving stock (Functor)

handleLocalStateOnly :: forall s x. Prog Void1 (Local s) (State s) x -> x
handleLocalStateOnly prog =
  handle @Void1 @(Local s) @(State s) @(StateC s) EndoAlgebra{pureE, callE, enterE} BaseAlgebra{callB, enterB} id prog
 where
  pureE :: a -> StateC s a
  pureE = pure
  callE :: State s (StateC s a) -> StateC s a
  callE = \case
    Swap f k -> swapState f >>= k
  enterE = \case
    Local localState prog -> do
      (prevState, _) <- swapState (const localState)
      k <- prog
      void $ swapState (const prevState)
      k
  swapState f = StateC (\(!s0) -> let !s1 = f s0 in (s1, (s0, s1)))
  callB :: Void1 a -> a
  callB = \case {}
  enterB :: Local s (StateC s x) -> x
  enterB = \case
    Local s prog -> snd $ runStateC prog s

b :: Integer -> (Integer, Integer)
b i = handleLocalStateOnly do
  x <- local i do
    modify (+ (1 :: Integer))
    modify (* 3)
    get
  y <- local x do
    modify (* 2)
    modify (+ 7)
    get
  pure (x, y)

-- >>> b 1
-- (6, 19)

-- Throw effect

data Throw e x = Throw e
  deriving stock (Functor)

throw :: a -> Prog (Throw a) scopes scopedAlgs x
throw = call . Throw

-- Catch effect

data Catch e x = Catch x (e -> x)
  deriving stock (Functor)

catch ::
  (Functor scopedAlgs, Functor algs) =>
  Prog scopedAlgs (Catch e) scopedAlgs x ->
  (e -> Prog scopedAlgs (Catch e) scopedAlgs x) ->
  Prog algs (Catch e) scopedAlgs x
catch action recovery = scoped $ (Catch action recovery)

handleThrowInsideCatch ::
  forall e x.
  Prog Void1 (Catch e) (Throw e) x ->
  x
handleThrowInsideCatch prog =
  handle EndoAlgebra{pureE, callE, enterE} BaseAlgebra{callB, enterB} id prog
 where
  callB :: forall a. Void1 a -> a
  callB = \case {}
  enterB :: forall a. Catch e (Either e a) -> a
  enterB = \case
    Catch prog recover ->
      case prog of
        Left e -> case recover e of
          -- This should not happen, but to prevent it we need a way to
          -- say that the recovery block in Catch must run in the parent scope
          Left _ -> error "Thrown inside top-level catch recovery"
          Right a -> a
        Right a -> a
  pureE = pure
  callE :: Throw e (Either e a) -> Either e a
  callE = \case
    Throw e -> Left e
  enterE :: Catch e (Either e (Either e a)) -> Either e a
  enterE = \case
    Catch prog recovery -> case prog of
      Left e -> join $ recovery e
      Right a -> a

throwInsideCatch :: String
throwInsideCatch = handleThrowInsideCatch do
  catch
    do throw 'a'
    \e -> pure $ "thrown: " <> [e]

throwInCatchRecovery :: String
throwInCatchRecovery = handleThrowInsideCatch do
  catch
    do throw 'a'
    \e -> throw e
