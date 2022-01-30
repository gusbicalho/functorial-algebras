{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE UndecidableInstances #-}

module Scratch where

import Control.Monad (ap)
import Data.Kind (Constraint, Type)
import GHC.OverloadedLabels (IsLabel (..))
import GHC.TypeLits (ErrorMessage (ShowType, Text, (:<>:)), Symbol, TypeError)

class IsAction lbl where
  type ActionInput lbl :: Type
  type ActionResult lbl :: Type

type Action :: Type -> Type -> Type
data Action lbl x = Action (ActionInput lbl) (ActionResult lbl -> x)
  deriving stock (Functor)

action :: ActionInput lbl -> (ActionResult lbl -> x) -> Action lbl x
action = Action

data Actions labels x where
  Here ::
    forall label moreLabels x.
    Action label x ->
    Actions (label ': moreLabels) x
  There ::
    forall label moreLabels x.
    Actions moreLabels x ->
    Actions (label ': moreLabels) x

instance Functor (Actions labels) where
  fmap f (Here action) = Here (fmap f action)
  fmap f (There sig) = There (fmap f sig)

class IsAction label => Inject label labels where
  inj :: Action label x -> Actions labels x

instance
  {-# OVERLAPPABLE #-}
  IsAction label =>
  Inject label (label ': moreLabels)
  where
  inj = Here

instance
  {-# OVERLAPPING #-}
  (IsAction label, Inject label moreLabels) =>
  Inject label (label2 ': moreLabels)
  where
  inj = There . inj

type Has :: [Type] -> [Type] -> Constraint
type family sig `Has` labels where
  sig `Has` '[] = ()
  sig `Has` (label ': moreLabels) = (Inject label sig, sig `Has` moreLabels)

--------

data Free sig x
  = Pure x
  | Call (Actions sig (Free sig x))
  deriving stock (Functor)

instance Applicative (Free sig) where
  pure = Pure
  (<*>) = ap

handle :: (Actions sig b -> b) -> (x -> b) -> Free sig x -> b
handle onCall onPure = go
 where
  go (Pure x) = onPure x
  go (Call action) = onCall (fmap go action)

instance Monad (Free sig) where
  action >>= g = handle Call g action

free ::
  forall (label :: Type) (sig :: [Type]).
  (IsAction label, sig `Has` '[label]) =>
  ActionInput label ->
  Free sig (ActionResult label)
free input = Call (inj @label (action input pure))

--------

data Get (s :: Type)
instance IsAction (Get s) where
  type ActionInput (Get s) = ()
  type ActionResult (Get s) = s

data Put (s :: Type)
instance IsAction (Put s) where
  type ActionInput (Put s) = s
  type ActionResult (Put s) = ()

data Throw
instance IsAction Throw where
  type ActionInput Throw = ()
  type ActionResult Throw = ()

data Fail
data Or (x :: Type)

instance IsAction Fail where
  type ActionInput Fail = ()
  type ActionResult Fail = ()

instance IsAction (Or x) where
  type ActionInput (Or x) = (x, x)
  type ActionResult (Or x) = x

what :: sig `Has` '[Throw, Fail, Get Word, Put Word] => Free sig ()
what = do
  free @Throw ()
  free @Fail ()
  w <- free @(Get Word) ()
  free @(Put Word) $ w + 1
