{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}

module SplitScopedProg.FunAlg where

import Control.Monad (ap, void)
import Data.Kind (Type)
import StateC (StateC (..))

-- Syntax tree for top-level and scoped programs

type Signature = Type -> Type

type Prog :: Signature -> Signature -> Signature -> Type -> Type
data Prog algs scopes scopedAlgs x where
  Pure :: x -> Prog algs scopes scopedAlgs x
  Call :: (algs (Prog algs scopes scopedAlgs x)) -> Prog algs scopes scopedAlgs x
  Enter :: scopes (ScopedProg scopedAlgs scopes (Prog algs scopes scopedAlgs x)) -> Prog algs scopes scopedAlgs x

instance (Functor algs, Functor scopes, Functor scopedAlgs) => Functor (Prog algs scopes scopedAlgs) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Call algOp) = Call (fmap (fmap f) algOp)
  fmap f (Enter innerOp) = Enter $ (fmap . fmap . fmap $ f) innerOp

type ScopedProg :: Signature -> Signature -> Type -> Type
data ScopedProg algs scopes x where
  PureE :: x -> ScopedProg algs scopes x
  CallE :: (algs (ScopedProg algs scopes x)) -> ScopedProg algs scopes x
  EnterE :: (scopes (ScopedProg algs scopes (ScopedProg algs scopes x))) -> ScopedProg algs scopes x
  deriving stock (Functor)

instance (Functor algs, Functor scopes, Functor scopedAlgs) => Applicative (Prog algs scopes scopedAlgs) where
  pure = Pure
  (<*>) = ap

instance (Functor algs, Functor scopes, Functor scopedAlgs) => Monad (Prog algs scopes scopedAlgs) where
  Pure x >>= k = k x
  Call algOp >>= k = Call (fmap (>>= k) algOp)
  Enter innerOp >>= k = Enter ((fmap . fmap) (>>= k) innerOp)

instance (Functor algs, Functor scopes) => Applicative (ScopedProg algs scopes) where
  pure = PureE
  (<*>) = ap

instance (Functor algs, Functor scopes) => Monad (ScopedProg algs scopes) where
  PureE x >>= k = k x
  CallE algOp >>= k = CallE (fmap (>>= k) algOp)
  EnterE scopedOp >>= k = EnterE (fmap (fmap (>>= k)) scopedOp)

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
  (forall x. ScopedProg scopedAlgs scopes x -> f x) ->
  BaseAlgebra algs scopes f b ->
  (a -> b) ->
  Prog algs scopes scopedAlgs a ->
  b
handleBase handleScoped BaseAlgebra{callB, enterB} gen = go
 where
  go :: Prog algs scopes scopedAlgs a -> b
  go (Pure a) = gen a
  go (Call algOp) = callB $ fmap go algOp
  go (Enter innerOp) = enterB (fmap (handleScoped . fmap go) innerOp)

handleScoped ::
  forall f x algs scopes.
  (Functor f, Functor algs, Functor scopes) =>
  EndoAlgebra algs scopes f ->
  ScopedProg algs scopes x ->
  f x
handleScoped EndoAlgebra{pureE, callE, enterE} = go
 where
  go :: forall x. ScopedProg algs scopes x -> f x
  go (PureE a) = pureE a
  go (CallE algOp) = callE (fmap go algOp)
  go (EnterE scopedOp) = enterE (fmap (go . fmap go) scopedOp)

handleE ::
  forall algs scopes f x.
  (Functor algs, Functor scopes, Monad f) =>
  EndoAlgebra algs scopes f ->
  Prog algs scopes algs x ->
  f x
handleE ealg@EndoAlgebra{pureE, callE, enterE} =
  handle ealg BaseAlgebra{callB = callE, enterB = enterE} pureE

-- Helpers to lift effect functors into Prog or ScopedProg

class
  (Monad p, Functor (AlgebraicSig p)) =>
  HasCall p
  where
  type AlgebraicSig p :: Signature
  call :: AlgebraicSig p (p x) -> p x

instance
  (Functor algs, Functor scopes, Functor scopedAlgs) =>
  HasCall (Prog algs scopes scopedAlgs)
  where
  type AlgebraicSig (Prog algs scopes scopedAlgs) = algs
  call = Call

instance
  (Functor algs, Functor scopes) =>
  HasCall (ScopedProg algs scopes)
  where
  type AlgebraicSig (ScopedProg algs scopes) = algs
  call = CallE

class
  (Monad p, Functor (ScopesSig p), Functor (ScopedAlgebraicSig p)) =>
  HasScoped p
  where
  type ScopesSig p :: Signature
  type ScopedAlgebraicSig p :: Signature
  scoped :: ScopesSig p (ScopedProg (ScopedAlgebraicSig p) (ScopesSig p) x) -> p x

instance
  (Functor algs, Functor scopes, Functor scopedAlgs) =>
  HasScoped (Prog algs scopes scopedAlgs)
  where
  type ScopesSig (Prog algs scopes scopedAlgs) = scopes
  type ScopedAlgebraicSig (Prog algs scopes scopedAlgs) = scopedAlgs
  scoped = Enter . fmap (fmap pure)

instance
  (Functor algs, Functor scopes) =>
  HasScoped (ScopedProg algs scopes)
  where
  type ScopesSig (ScopedProg algs scopes) = scopes
  type ScopedAlgebraicSig (ScopedProg algs scopes) = algs
  scoped = EnterE . fmap (fmap pure)

-- State effect

data State s x = Swap (s -> s) ((s, s) -> x)
  deriving stock (Functor)

data Local s x = Local s x
  deriving stock (Functor)

swap :: (HasCall p, AlgebraicSig p ~ State s) => (s -> s) -> p (s, s)
swap f = call (Swap f pure)

modify :: (HasCall p, AlgebraicSig p ~ State s) => (s -> s) -> p ()
modify f = void (swap f)

get :: (HasCall p, AlgebraicSig p ~ State s) => p s
get = snd <$> swap id

put :: (HasCall p, AlgebraicSig p ~ State s) => s -> p ()
put s = void $ swap (const s)

local :: (HasScoped p, ScopesSig p ~ Local s) => s -> ScopedProg (ScopedAlgebraicSig p) (ScopesSig p) x -> p x
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
