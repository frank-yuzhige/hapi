{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.AASTG.Analysis.Cycle where

import Test.HAPI.AASTG.Core ( AASTG (AASTG, getStart), NodeID, edgesFrom, endNode, startNode, allNodes, changeEdgeNode )
import Test.HAPI.Effect.Eff ( runEnv )
import Data.IntSet ( IntSet, empty, member )
import Control.Carrier.State.Church (runState, run)
import Control.Effect.State (gets, State, modify)
import Control.Algebra (Has)
import Control.Monad (forM, forM_)
import Test.HAPI.AASTG.Effect.Build (BuildAASTG, newNode, setNode, currNode, newEdge, runBuildAASTG)
import Data.Functor.Contravariant (phantom)
import Control.Effect.Labelled (HasLabelled)
import Data.IntMap (IntMap)

import qualified Control.Effect.State.Labelled as LS
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS


isCyclicAASTG :: AASTG api c -> [NodeID]
isCyclicAASTG aastg@(AASTG s _ _) = run $ runState (\s a -> return a) IS.empty $ go s
  where
    go :: Has (State IntSet) sig m => Int -> m [NodeID]
    go i = do
      visited <- gets (IS.member i)
      if visited then return [i] else do
        fmap concat $ forM (edgesFrom i aastg) $
          \e -> go (endNode e)

data ACYCLIC

unrollCycle :: forall api c. Int -> AASTG api c -> AASTG api c
unrollCycle maxDepth aastg
  = runEnv
  $ runBuildAASTG @api @c
  $ unroll
  where
    unroll :: ( Has (BuildAASTG api c) sig m)
          => m ()
    unroll = trav maxDepth (getStart aastg)
      where
        trav 0 _ = return ()
        trav d i = do
          i' <- currNode @api @c
          forM_ (edgesFrom i aastg) $ \edge -> do
            let e = endNode edge
            e' <- newNode @api @c
            setNode @api @c e'
            newEdge (changeEdgeNode i' e' edge)
            trav (d - 1) e
            setNode @api @c i'
