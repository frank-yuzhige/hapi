{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Analysis.Rename where

import Test.HAPI.AASTG.Core (AASTG (AASTG), NodeID, Edge (..), allNodes)
import Data.IntMap (IntMap)
import qualified Data.Map as M
import qualified Data.IntMap as IM

type NodeRenameMap = IntMap NodeID  -- NodeID -> NodeID

maxNodeID :: AASTG api c -> NodeID
maxNodeID (AASTG start fs bs) = maximum (start : M.keys fs <> M.keys bs)

minNodeID :: AASTG api c -> NodeID
minNodeID (AASTG start fs bs) = minimum (start : M.keys fs <> M.keys bs)

renameNodes :: NodeRenameMap -> AASTG api c -> AASTG api c
renameNodes nrm aastg@(AASTG start fs bs) = AASTG (nrm IM.! start) fs' bs'
  where
    fs' = M.map (renameNodesInEdge nrm <$>) fs
    bs' = M.map (renameNodesInEdge nrm <$>) bs

renameNodesInEdge :: NodeRenameMap -> Edge api c -> Edge api c
renameNodesInEdge nrm = \case
  Update s e k a          -> Update  (look s) (look e) k a
  Forget s e k            -> Forget  (look s) (look e) k
  Assert s e x y          -> Assert  (look s) (look e) x y
  APICall s e mx api args -> APICall (look s) (look e) mx api args
  where
    look i = nrm IM.! i

renameNodesViaOffset :: Int -> AASTG api c -> AASTG api c
renameNodesViaOffset offset aastg = renameNodes (IM.fromList [(n, n + offset) | n <- allNodes aastg]) aastg

normalizeNodes :: Int -> AASTG api c -> AASTG api c
normalizeNodes offset aastg = renameNodes (IM.fromAscList (allNodes aastg `zip` [offset..])) aastg

