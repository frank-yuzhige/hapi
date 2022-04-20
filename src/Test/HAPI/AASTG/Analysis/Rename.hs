{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Analysis.Rename where

import Test.HAPI.AASTG.Core (AASTG (AASTG), NodeID, Edge (..), allNodes)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Maybe (fromMaybe)

type NodeRenameMap = IntMap NodeID  -- NodeID -> NodeID

maxNodeID :: AASTG api c -> NodeID
maxNodeID (AASTG start fs bs) = maximum (start : IM.keys fs <> IM.keys bs)

minNodeID :: AASTG api c -> NodeID
minNodeID (AASTG start fs bs) = minimum (start : IM.keys fs <> IM.keys bs)

renameNodes :: NodeRenameMap -> AASTG api c -> AASTG api c
renameNodes nrm aastg@(AASTG start fs bs) = AASTG (nrm IM.! start) fs' bs'
  where
    fs' = IM.mapKeys (nrm IM.!) $ IM.map (renameNodesInEdge nrm <$>) fs
    bs' = IM.mapKeys (nrm IM.!) $ IM.map (renameNodesInEdge nrm <$>) bs

renameNodesInEdge :: NodeRenameMap -> Edge api c -> Edge api c
renameNodesInEdge nrm = \case
  Update   s e k a          -> Update   (look s) (look e) k a
  Forget   s e k            -> Forget   (look s) (look e) k
  Assert   s e x y          -> Assert   (look s) (look e) x y
  APICall  s e mx api args  -> APICall  (look s) (look e) mx api args
  Redirect s e              -> Redirect (look s) (look e)
  where
    look i = fromMaybe i $ nrm IM.!? i

renameNodesViaOffset :: Int -> AASTG api c -> AASTG api c
renameNodesViaOffset offset aastg = renameNodes (IM.fromList [(n, n + offset) | n <- allNodes aastg]) aastg

normalizeNodes :: Int -> AASTG api c -> AASTG api c
normalizeNodes offset aastg = renameNodes (IM.fromList (allNodes aastg `zip` [offset..])) aastg

