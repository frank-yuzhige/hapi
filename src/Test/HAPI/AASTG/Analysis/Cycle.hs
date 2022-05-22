{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Analysis.Cycle where

import Test.HAPI.AASTG.Core ( AASTG (AASTG, getStart), NodeID, edgesFrom, endNode, startNode, allNodes, changeEdgeNode )
import Test.HAPI.Effect.Eff ( runEnv )
import Data.IntSet ( IntSet, empty, member )
import Control.Carrier.State.Church (runState, run)
import Control.Effect.State (gets, State, modify)
import Control.Algebra (Has)
import Control.Monad (forM, forM_)
import Test.HAPI.AASTG.Effect.Build (BuildAASTG, newNode, currNode, runBuildAASTG, sSetNode, sNewEdge, sNewNode, sCurrNode)
import Data.Functor.Contravariant (phantom)
import Control.Effect.Labelled (HasLabelled, runLabelled)
import Data.IntMap (IntMap)

import qualified Control.Effect.State.Labelled as LS
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Test.HAPI.AASTG.Analysis.ProcType (ProcType (..), UnboundedProcTypeMap (coerce2Bounded), (!*))


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
    unroll :: ( Has (BuildAASTG api c) sig m )
          => m ()
    unroll = trav maxDepth (getStart aastg) IS.empty
      where
        trav 0 _ _ = return ()
        trav d i h = do
          i' <- sCurrNode @api @c
          forM_ (edgesFrom i aastg) $ \edge -> do
            let e = endNode edge
            e' <- sNewNode @api @c
            sSetNode @api @c e'
            sNewEdge (changeEdgeNode i' e' edge)
            trav (d - 1) e h
            sSetNode @api @c i'

isAcyclicType :: ProcType -> Bool
isAcyclicType = \case
  Mu x t  -> isAcyclicType t
  SVar x  -> False
  Act _ t -> isAcyclicType t
  Par ts  -> all isAcyclicType ts
  Zero    -> True

isAcyclicTypeUB :: UnboundedProcTypeMap -> ProcType -> Bool
isAcyclicTypeUB uptm = go IS.empty
  where
    go history = \case
      Mu x t  -> go (IS.insert x history) t
      SVar x | x `IS.member` history -> False
             | otherwise             -> go (IS.insert x history) (uptm !* x)
      Act _ t -> go history t
      Par ts  -> all (go history) ts
      Zero    -> True

acyclicNodes :: UnboundedProcTypeMap -> [NodeID]
acyclicNodes uptm = [k | k <- IM.keys (coerce2Bounded uptm), isAcyclicTypeUB uptm (uptm !* k) ]
