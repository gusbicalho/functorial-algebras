module StateC where

import Control.Monad (ap)

newtype StateC s a = StateC {runStateC :: s -> (s, a)}
  deriving stock (Functor)

instance Applicative (StateC s) where
  pure a = StateC (\s -> (s, a))
  (<*>) = ap

instance Monad (StateC s) where
  stateA >>= k = StateC $ \s ->
    let !(!s1, !a) = runStateC stateA s
     in runStateC (k a) s1
