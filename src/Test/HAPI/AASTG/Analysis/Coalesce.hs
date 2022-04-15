{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Analysis.Coalesce where

import Test.HAPI.AASTG.Core (AASTG (AASTG, getEdgesFrom, getEdgesTo), NodeID, Edge (Update, Forget, Assert, APICall), allNodes, edgesFrom, edgesTo2EdgesFrom)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes, maxNodeID, renameNodesInEdge)
import Test.HAPI.AASTG.Analysis.PathExtra (NodePathMap, effectiveSubpath)

coalesceAASTGs :: AASTG api c -> AASTG api c -> Maybe (AASTG api c)
coalesceAASTGs a1 a2 = undefined
  where
    a1' = normalizeNodes 0                   a1
    a2' = normalizeNodes (maxNodeID a1' + 1) a2
    start = AASTG 0 (getEdgesFrom a1' ) (getEdgesTo a1')

directCoalesceState :: NodeID -> NodeID -> AASTG api c -> AASTG api c
directCoalesceState er ee aastg = AASTG 0 fs bs
  where
    fs = M.delete ee . M.adjust (<> edgesFrom ee aastg) er $ getEdgesFrom aastg
    bs = edgesTo2EdgesFrom fs

upperSubNode :: NodePathMap api c -> NodeID -> NodeID -> Bool
upperSubNode ctx n1 n2 = and [or [ isJust $ p1 `effectiveSubpath` p2 | p2 <- ctx M.! n2] | p1 <- ctx M.! n1]
