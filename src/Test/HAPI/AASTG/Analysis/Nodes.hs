{-# LANGUAGE TypeApplications #-}
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


type UnrelatedNodeMap  = HashMap NodeID [NodeID]
type UnrelatedNodeMap' = HashMap NodeID (HashSet NodeID)

-- | 2 nodes are unrelated, iff there exists no path that passes n1 and n2.
-- Return a HashMap that maps each node to a list of unrelated nodes.
unrelatedNodeMap :: AASTG api c -> UnrelatedNodeMap
unrelatedNodeMap aastg = HM.map (HS.toList . HS.difference nodes) relatives
  where
    nodes = HS.fromList $ allNodes aastg
    children = run
             . runState (\s a -> return s) HM.empty
             $ calcChildren (getStart aastg)
    relatives = run
              . runState @UnrelatedNodeMap' (\s a -> return s) children
              $ addParents [] (getStart aastg)

    calcChildren :: Has (State UnrelatedNodeMap') sig m => NodeID -> m (HashSet NodeID)
    calcChildren n = do
      computed <- gets @UnrelatedNodeMap' (HM.member n)
      if computed then gets (HM.! n) else do
        allChildren <- forM (edgesFrom n aastg) $ \edge -> do
          calcChildren $ endNode edge
        let ans = HS.insert n $ HS.unions allChildren
        modify $ HM.insert n ans
        return ans

    addParents :: Has (State UnrelatedNodeMap') sig m => [NodeID] -> NodeID -> m ()
    addParents trace n = do
      let trace' = n : trace
      modify $ HM.update (\s -> Just $ foldr HS.insert s trace') n
      forM_ (edgesFrom n aastg) $ \edge -> do
        addParents trace' (endNode edge)
