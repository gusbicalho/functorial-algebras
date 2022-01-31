module FunctorialAlgebras.ThrowCatch where

import Control.Applicative ((<|>))
import Control.Monad (join)
import Data.Maybe qualified as Maybe
import FunctorialAlgebras (
  BaseAlgebra (..),
  EndoAlgebra (..),
  Prog,
  call,
  handle,
  handleE,
  scoped,
 )

data Throw x = Throw
  deriving stock (Functor)

throw :: Prog Throw scopes x
throw = call Throw

data Catch x = Catch x x
  deriving stock (Functor)

catch :: Functor algs => Prog algs Catch x -> Prog algs Catch x -> Prog algs Catch x
catch h r = scoped $ Catch h r

prog :: Integer -> Prog Throw Catch Integer
prog divisor = do
  (12 `safeDiv` divisor) `catch` pure 42
 where
  a `safeDiv` b
    | b == 0 = throw
    | otherwise = pure $ a `div` b

handleErrorsFallback :: x -> Prog Throw Catch x -> x
handleErrorsFallback finalRecovery =
  handle
    EndoAlgebra
      { pureE = Just
      , callE = \case
          Throw -> Nothing
      , enterE = \case
          Catch (Just k) _ -> k
          Catch Nothing recovery -> join recovery
      }
    BaseAlgebra
      { callB = \case
          Throw -> finalRecovery
      , enterB = \case
          Catch comp recovery -> Maybe.fromMaybe finalRecovery (comp <|> recovery)
      }
    id

handleErrorsMaybe :: Prog Throw Catch x -> Maybe x
handleErrorsMaybe =
  handleE
    EndoAlgebra
      { pureE = Just
      , callE = \case
          Throw -> Nothing
      , enterE = \case
          Catch (Just k) _ -> k
          Catch Nothing recovery -> join recovery
      }
