{-# LANGUAGE BlockArguments #-}

module FunctorialAlgebras where

import Control.Applicative ((<|>))
import Control.Monad (ap, join, when)
import Data.Foldable (fold)
import Data.Kind (Type)
import Data.Maybe qualified as Maybe
import Debug.Trace qualified as Trace

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

--------

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

handleThrowCatch :: Prog Throw Catch x -> Maybe x
handleThrowCatch (Pure x) = Just x
handleThrowCatch (Call algOp) = case algOp of
  Throw -> Nothing
handleThrowCatch (Enter scopedOp) = case scopedOp of
  Catch comp recovery -> (handleThrowCatch comp <|> handleThrowCatch recovery) >>= handleThrowCatch

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

---------
data Choice x = Choice [x]
  deriving stock (Functor)

fail' :: Prog Choice scopes x
fail' = call (Choice [])

choice :: [Prog Choice scopes x] -> Prog Choice scopes x
choice paths = call (Choice paths)

data Once x = Once x
  deriving stock (Functor)

once :: Functor algs => Prog algs Once x -> Prog algs Once x
once x = scoped (Once x)

nonDetAlg :: EndoAlgebra Choice Once []
nonDetAlg = EndoAlgebra{pureE, callE, enterE}
 where
  pureE x = [x]
  callE (Choice paths) = concat paths
  enterE (Once xss) = case xss of
    [] -> []
    (xs : _) -> xs

handleNonDet :: Prog Choice Once x -> [x]
handleNonDet = handleE nonDetAlg

nonDetProg :: Prog Choice Once (Integer, Integer, Char, Integer)
nonDetProg = do
  x <- choice [pure 2, pure 4]
  y <-
    choice
      [ fail'
      , once do
          choice
            [ pure 3
            , pure 7
            ]
      , pure 13
      ]
  pure (x, y, '=', x * y)

data SearchStrategy x = DFS x | BFS x | DBS Word x
  deriving stock (Functor)

dfs :: Functor algs => Prog algs SearchStrategy x -> Prog algs SearchStrategy x
dfs x = scoped (DFS x)

bfs :: Functor algs => Prog algs SearchStrategy x -> Prog algs SearchStrategy x
bfs x = scoped (BFS x)

dbs :: Functor algs => Word -> Prog algs SearchStrategy x -> Prog algs SearchStrategy x
dbs depth x = scoped (DBS depth x)

data SearchStrategyC a = SSC {getDFS :: [a], getBFS :: [[a]], getDBS :: (Word -> [a])}
  deriving stock (Functor)

instance Semigroup (SearchStrategyC a) where
  SSC dfsA bfsA dbsA <> SSC dfsB bfsB dbsB =
    SSC (dfsA <> dfsB) (merge bfsA bfsB) (dbsA <> dbsB)
   where
    merge xss [] = xss
    merge [] yss = yss
    merge (xs : xss) (ys : yss) = (xs <> ys) : merge xss yss

instance Monoid (SearchStrategyC a) where
  mempty = SSC [] [] (const [])

handleSearch :: forall x. Prog Choice SearchStrategy x -> [x]
handleSearch =
  handle @Choice @SearchStrategy @SearchStrategyC @x @[x] EndoAlgebra{pureE, callE, enterE} BaseAlgebra{callB, enterB} gen
 where
  gen = pure
  pureE x = SSC [x] [[x]] (const [x])
  callE = \case
    Choice sscs ->
      SSC
        (fold (fmap getDFS sscs))
        (foldr merge [] (fmap getBFS sscs))
        (\depth -> if depth == 0 then [] else foldMap (\ssc -> getDBS ssc (depth - 1)) sscs)
   where
    merge xss [] = xss
    merge [] yss = yss
    merge (xs : xss) (ys : yss) = (xs <> ys) : merge xss yss
  enterE :: SearchStrategy (SearchStrategyC (SearchStrategyC a)) -> SearchStrategyC a
  enterE = \case
    DFS (SSC dfs _ _) ->
      let paths = concat (fmap getDFS dfs)
       in SSC paths [] (const [])
    BFS (SSC _ bfs _) ->
      let paths = fold (fmap getBFS (fold bfs))
       in SSC [] paths (const [])
    DBS depth (SSC _ _ dbs) -> foldMap (\(SSC _ _ dbs) -> SSC [] [] dbs) (dbs depth)
  callB = \case
    Choice paths -> concat paths
  enterB :: SearchStrategy (SearchStrategyC [x]) -> [x]
  enterB =
    concat . \case
      DFS (SSC dfs _ _) -> dfs
      BFS (SSC _ bfs _) -> concat bfs
      DBS depth (SSC _ _ dbs) -> dbs depth

-- a :: [(Integer)]
a strategy = handleSearch $ strategy do
  a <- choice [choice [pure 3, pure 4], pure 5, pure 6]
  Trace.traceM $ "a: " <> show a
  b <- choice [pure 7, pure 8]
  Trace.traceM $ "b: " <> show b
  let r :: Integer = a + b
  when (even r) fail'
  Trace.traceM $ "r: " <> show r
  pure (a, b, r)
