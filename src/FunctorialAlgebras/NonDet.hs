{-# LANGUAGE BlockArguments #-}

module FunctorialAlgebras.NonDet where

import Control.Monad (when)
import Data.Foldable (fold)
import Debug.Trace qualified as Trace
import FunctorialAlgebras (BaseAlgebra (..), EndoAlgebra (..), Prog, call, handle, handleE, scoped)

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

data SearchStrategy x
  = DFS x
  | {-
    pretty sure i did not get the impl for this one right
    | BFS x
    -}
    DBS Word x
  deriving stock (Functor)

dfs :: Functor algs => Prog algs SearchStrategy x -> Prog algs SearchStrategy x
dfs x = scoped (DFS x)

-- bfs :: Functor algs => Prog algs SearchStrategy x -> Prog algs SearchStrategy x
-- bfs x = scoped (BFS x)

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
  handle EndoAlgebra{pureE, callE, enterE} BaseAlgebra{callB, enterB} gen
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
      fold dfs
    -- BFS (SSC _ bfs _) ->
    --   fold $ fold bfs
    DBS depth (SSC _ _ dbs) ->
      fold (dbs depth)
  callB = \case
    Choice paths -> concat paths
  enterB :: SearchStrategy (SearchStrategyC [x]) -> [x]
  enterB =
    concat . \case
      DFS (SSC dfs _ _) -> dfs
      -- BFS (SSC _ bfs _) -> concat bfs
      DBS depth (SSC _ _ dbs) -> dbs depth

-- a :: [(Integer)]
a ::
  Functor scopes =>
  ( Prog Choice scopes (Integer, Integer, Integer) ->
    Prog Choice SearchStrategy x
  ) ->
  [x]
a strategy = handleSearch $ strategy do
  a <- choice [choice [pure 3, pure 4], pure 5, pure 6]
  Trace.traceM $ "a: " <> show a
  b <- choice [pure 7, pure 8]
  Trace.traceM $ "b: " <> show b
  let r :: Integer = a + b
  when (even r) fail'
  Trace.traceM $ "r: " <> show r
  pure (a, b, r)

type StrategyScope =
  forall x.
  Prog Choice SearchStrategy x ->
  Prog Choice SearchStrategy x

b ::
  StrategyScope ->
  StrategyScope ->
  [(Integer, Char, String, Bool)]
b s1 s2 = handleSearch $ s1 do
  a <- choice [pure (1 :: Integer), pure 2]
  Trace.traceM $ "a: " <> show a
  b <- choice [pure 'a', pure 'b']
  Trace.traceM $ "b: " <> show b
  (c, d) <- s2 do
    c <- choice [pure "foo", pure "bar"]
    Trace.traceM $ "c: " <> show c
    d <- choice [pure True, pure False]
    Trace.traceM $ "d: " <> show d
    pure (c, d)
  pure (a, b, c, d)
