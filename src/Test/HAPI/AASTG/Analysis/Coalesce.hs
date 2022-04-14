{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Analysis.Coalesce where

import Test.HAPI.AASTG.Core (AASTG (AASTG, getEdgesFrom, getEdgesTo), NodeID, Edge (Update, Forget, Assert, APICall), allNodes, edgesFrom, edgesTo2EdgesFrom)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes, maxNodeID, renameNodesInEdge)

coalesceAASTGs :: AASTG api c -> AASTG api c -> Maybe (AASTG api c)
coalesceAASTGs a1 a2 = undefined
  where
    a1' = normalizeNodes 0                   a1
    a2' = normalizeNodes (maxNodeID a1' + 1) a2
    start = AASTG 0 (getEdgesFrom a1' ) (getEdgesTo a1')


unsafeCoalesceState :: NodeID -> NodeID -> AASTG api c -> AASTG api c
unsafeCoalesceState er ee aastg = AASTG 0 fs bs
  where
    fs = M.delete ee . M.adjust (<> edgesFrom ee aastg) er $ getEdgesFrom aastg
    bs = edgesTo2EdgesFrom fs


