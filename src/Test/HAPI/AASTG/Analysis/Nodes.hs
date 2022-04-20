{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Test.HAPI.AASTG.Analysis.Nodes where

import Data.HashMap.Strict (HashMap)
import Test.HAPI.AASTG.Core (NodeID, AASTG (getStart), allNodes, endNode, edgesFrom)
import Data.HashSet (HashSet)
import Control.Algebra (Has, run)
import Control.Effect.State (State, gets, modify)
import Control.Monad (forM_, forM)

import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import Control.Carrier.State.Church (runState)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IM

type NodeRelationMap = IntMap (HashSet NodeID)

childrenNodes :: AASTG api c -> NodeRelationMap
childrenNodes aastg = run $ runState (\s a -> return s) IM.empty $ calcChildren (getStart aastg)
  where
    calcChildren :: Has (State NodeRelationMap) sig m => NodeID -> m (HashSet NodeID)
    calcChildren n = do
      computed <- gets @NodeRelationMap (IM.member n)
      if computed then gets (IM.! n) else do
        allChildren <- mapM (calcChildren . endNode) (edgesFrom n aastg)
        let ans = HS.insert n $ HS.unions allChildren
        modify $ IM.insert n ans
        return ans

type UnrelatedNodeMap  = IntMap [NodeID]

-- | 2 nodes are unrelated, iff there exists no path that passes n1 and n2.
-- Return a HashMap that maps each node to a list of unrelated nodes.
unrelatedNodeMap :: AASTG api c -> UnrelatedNodeMap
unrelatedNodeMap aastg = IM.map (HS.toList . HS.difference nodes) relatives
  where
    nodes = HS.fromList $ allNodes aastg
    children = childrenNodes aastg
    relatives = run
              . runState @NodeRelationMap (\s a -> return s) children
              $ addParents [] (getStart aastg)

    addParents :: Has (State NodeRelationMap) sig m => [NodeID] -> NodeID -> m ()
    addParents trace n = do
      let trace' = n : trace
      modify $ IM.update (\s -> Just $ foldr HS.insert s trace') n
      forM_ (edgesFrom n aastg) $ \edge -> do
        addParents trace' (endNode edge)

type NodeDepthMap  = IntMap Int

nodeDepthMap :: AASTG api c -> NodeDepthMap
nodeDepthMap aastg = run $ runState (\s _ -> return s) IM.empty $ visit (getStart aastg) 0
  where
    visit n h = do
      visited <- gets @NodeDepthMap (IM.member n)
      if visited then return () else do
        modify @NodeDepthMap (IM.insert n h)
        forM_ [endNode e | e <- edgesFrom n aastg] $ \e -> do
          visit e (h + 1)
