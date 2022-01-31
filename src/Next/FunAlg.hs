{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}

module Next.FunAlg where

import Control.Monad (ap, void, (>=>))
import Data.Kind (Type)

-- Syntax tree for top-level and scoped programs

type Signature = Type -> Type

type Prog :: Signature -> Signature -> Signature -> Type -> Type
data Prog algs scopes scopedAlgs x where
  Pure :: x -> Prog algs scopes scopedAlgs x
  Call :: (algs (Prog algs scopes scopedAlgs x)) -> Prog algs scopes scopedAlgs x
  Enter :: scopes (ScopedProg scopedAlgs scopes a) -> (a -> Prog algs scopes scopedAlgs x) -> Prog algs scopes scopedAlgs x

instance (Functor algs) => Functor (Prog algs scopes scopedAlgs) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Call algOp) = Call (fmap (fmap f) algOp)
  fmap f (Enter innerOp k) = Enter innerOp (fmap f . k)

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
  Enter innerOp k1 >>= k = Enter innerOp (k1 >=> k)

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
  go (Enter innerOp k) = enterB (fmap (handleScoped . fmap (go . k)) innerOp)

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
  (Monad p, Functor scopes, Functor algs, Functor scopedAlgs) =>
  IsProg p algs scopes scopedAlgs
    | p -> algs scopes scopedAlgs
  where
  call :: algs (p x) -> p x
  scoped :: scopes (ScopedProg scopedAlgs scopes x) -> p x

instance
  (Functor algs, Functor scopes, Functor scopedAlgs) =>
  IsProg (Prog algs scopes scopedAlgs) algs scopes scopedAlgs
  where
  call = Call
  scoped op = Enter op pure

instance
  (Functor algs, Functor scopes) =>
  IsProg (ScopedProg algs scopes) algs scopes algs
  where
  call = CallE
  scoped = EnterE . fmap (fmap pure)

-- State carrier

newtype StateC s a = StateC {runStateC :: s -> (s, a)}
  deriving stock (Functor)

instance Applicative (StateC s) where
  pure a = StateC (\s -> (s, a))
  (<*>) = ap

instance Monad (StateC s) where
  stateA >>= k = StateC $ \s ->
    let !(!s1, !a) = runStateC stateA s
     in runStateC (k a) s1

-- State effect

data State s x = Swap (s -> s) ((s, s) -> x)
  deriving stock (Functor)

data Local s x = Local s x
  deriving stock (Functor)

swap :: IsProg p (State s) scopes scopedAlgs => (s -> s) -> p (s, s)
swap f = call (Swap f pure)

modify :: IsProg f (State s) scopes scopedAlgs => (s -> s) -> f ()
modify f = void (swap f)

get :: IsProg p (State s) scopes scopedAlgs => p s
get = snd <$> swap id

put :: IsProg f (State s) scopes scopedAlgs => s -> f ()
put s = void $ swap (const s)

local :: IsProg p algs (Local s) scopedAlgs => s -> ScopedProg scopedAlgs (Local s) x -> p x
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
