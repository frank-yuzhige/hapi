{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Test.HAPI.AASTG.Analysis.Nodes where

import Data.HashMap.Strict (HashMap)
import Test.HAPI.AASTG.Core (NodeID, AASTG (getStart, AASTG), allNodes, endNode, edgesFrom, edgesFrom2EdgesTo)
import Data.HashSet (HashSet)
import Control.Algebra (Has, run)
import Control.Effect.State (State, gets, modify)
import Control.Monad (forM_, forM)
import Control.Carrier.State.Church (runState)
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM

type NodeSet         = IntSet
type NodeRelationMap = IntMap NodeSet

childrenNodes :: AASTG api c -> NodeRelationMap
childrenNodes aastg = run $ runState (\s a -> return s) IM.empty $ calcChildren IS.empty (getStart aastg)
  where
    calcChildren :: Has (State NodeRelationMap) sig m => NodeSet -> NodeID -> m NodeSet
    calcChildren visited n = do
      computed <- gets @NodeRelationMap (IM.member n)
      if computed then gets (IM.! n) else
        if IS.member n visited then return IS.empty else do
          allChildren <- mapM (calcChildren (IS.insert n visited) . endNode) (edgesFrom n aastg)
          let ans = IS.insert n $ IS.unions allChildren
          modify $ IM.insert n ans
          return ans

type UnrelatedNodeMap  = IntMap [NodeID]

-- | 2 nodes are unrelated, iff there exists no path that passes n1 and n2.
-- Return a HashMap that maps each node to a list of its unrelated nodes.
unrelatedNodeMap :: AASTG api c -> UnrelatedNodeMap
unrelatedNodeMap aastg = IM.map (IS.toList . IS.difference nodes) relatives
  where
    nodes = IS.fromList $ allNodes aastg
    children = childrenNodes aastg
    relatives = run
              . runState @NodeRelationMap (\s a -> return s) children
              $ addParents IS.empty (getStart aastg)

    addParents :: Has (State NodeRelationMap) sig m => NodeSet -> NodeID -> m ()
    addParents trace n
      | IS.member n trace = return ()
      | otherwise = do
        let trace' = IS.insert n trace
        modify $ IM.update (\s -> Just $ IS.union s trace') n
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

dropOrphanNodes :: AASTG api c -> AASTG api c
dropOrphanNodes aastg@(AASTG s fs _) = AASTG s fs' (edgesFrom2EdgesTo fs)
  where
    un = unrelatedNodeMap aastg
    fs' = foldr IM.delete fs (un IM.! s)
