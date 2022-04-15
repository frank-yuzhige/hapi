{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Analysis.Coalesce where

import Test.HAPI.AASTG.Core (AASTG (AASTG, getEdgesFrom, getEdgesTo), NodeID, Edge (Update, Forget, Assert, APICall), allNodes, edgesFrom, edgesTo2EdgesFrom)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM
import Data.Maybe (fromMaybe, isJust)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes, maxNodeID, renameNodesInEdge)
import Test.HAPI.AASTG.Analysis.PathExtra (NodePathMap, effectiveSubpath)
import Test.HAPI.AASTG.Analysis.Dependence (pathDeps, pathDegradedDeps)
import Test.HAPI.AASTG.Analysis.Path (Path(pathCalls))

coalesceAASTGs :: AASTG api c -> AASTG api c -> Maybe (AASTG api c)
coalesceAASTGs a1 a2 = undefined
  where
    a1' = normalizeNodes 0                   a1
    a2' = normalizeNodes (maxNodeID a1' + 1) a2
    start = AASTG 0 (getEdgesFrom a1' ) (getEdgesTo a1')

directCoalesceState :: NodeID -> NodeID -> AASTG api c -> AASTG api c
directCoalesceState er ee aastg = AASTG 0 fs bs
  where
    fs = HM.delete ee . HM.adjust (<> edgesFrom ee aastg) er $ getEdgesFrom aastg
    bs = edgesTo2EdgesFrom fs

upperSubNode :: NodePathMap api c -> NodeID -> NodeID -> Bool
upperSubNode ctx n1 n2 = and [or [isJust $ p1 ~<=~ p2 | p2 <- ctx HM.! n2] | p1 <- ctx HM.! n1]
  where
    (~<=~) = effectiveSubpath (deps HM.!) (degs HM.!) (calls HM.!)
    paths = concat $ HM.elems ctx
    deps  = HM.fromList [(path, pathDeps         path) | path <- paths]
    degs  = HM.fromList [(path, pathDegradedDeps path) | path <- paths]
    calls = HM.fromList [(path, pathCalls        path) | path <- paths]

