{-# LANGUAGE BlockArguments #-}

module FunctorialAlgebras where

import Control.Monad (ap)
import Data.Kind (Type)

type Signature = Type -> Type

type Prog :: Signature -> Signature -> Type -> Type
data Prog algs scopes x
  = Pure x
  | Call (algs (Prog algs scopes x))
  | Enter (scopes (Prog algs scopes (Prog algs scopes x)))
  deriving stock (Functor)

call :: algs (Prog algs scopes x) -> Prog algs scopes x
call = Call

scoped :: (Functor scopes, Functor algs) => scopes (Prog algs scopes x) -> Prog algs scopes x
scoped = Enter . fmap (fmap pure)

instance (Functor algs, Functor scopes) => Applicative (Prog algs scopes) where
  pure = Pure
  (<*>) = ap

instance (Functor algs, Functor scopes) => Monad (Prog algs scopes) where
  Pure x >>= k = k x
  Call algOp >>= k = Call (fmap (>>= k) algOp)
  Enter scopedOp >>= k = Enter (fmap (fmap (>>= k)) scopedOp)

-------

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
  forall algs scopes f a b.
  (Functor algs, Functor scopes, Functor f) =>
  EndoAlgebra algs scopes f ->
  BaseAlgebra algs scopes f b ->
  (a -> b) ->
  Prog algs scopes a ->
  b
handle ealg = handleBase (handleScoped ealg)

handleBase ::
  forall algs scopes f a b.
  (Functor algs, Functor scopes, Functor f) =>
  (forall x. Prog algs scopes x -> f x) ->
  BaseAlgebra algs scopes f b ->
  (a -> b) ->
  Prog algs scopes a ->
  b
handleBase handleScoped BaseAlgebra{callB, enterB} gen = go
 where
  go :: Prog algs scopes a -> b
  go (Pure a) = gen a
  go (Call algOp) = callB $ fmap go algOp
  go (Enter scopedOp) = enterB (fmap (handleScoped . fmap go) scopedOp)

handleScoped ::
  forall f x algs scopes.
  (Functor f, Functor algs, Functor scopes) =>
  EndoAlgebra algs scopes f ->
  Prog algs scopes x ->
  f x
handleScoped EndoAlgebra{pureE, callE, enterE} = go
 where
  go :: forall x. Prog algs scopes x -> f x
  go (Pure a) = pureE a
  go (Call algOp) = callE (fmap go algOp)
  go (Enter scopedOp) = enterE (fmap (go . fmap go) scopedOp)

handleE ::
  (Functor algs, Functor scopes, Functor f) =>
  EndoAlgebra algs scopes f ->
  Prog algs scopes x ->
  f x
handleE ealg@EndoAlgebra{pureE, callE, enterE} =
  handle ealg BaseAlgebra{callB = callE, enterB = enterE} pureE
