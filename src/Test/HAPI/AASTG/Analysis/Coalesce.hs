{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Analysis.Coalesce where

import Test.HAPI.AASTG.Core (AASTG (AASTG, getEdgesFrom, getEdgesTo), NodeID, Edge (Update, Forget, Assert, APICall), allNodes, edgesFrom, edgesTo2EdgesFrom)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes, maxNodeID, renameNodesInEdge)
import Test.HAPI.AASTG.Analysis.PathExtra (NodePathMap, effectiveSubpath, getPathMap)
import Test.HAPI.AASTG.Analysis.Dependence (pathDeps, pathDegradedDeps, DependenceMap, DegradedDepMap)
import Test.HAPI.AASTG.Analysis.Path (Path(pathCalls), APath)
import Data.List (partition)
import Data.IntMap (IntMap)
import Data.Maybe (fromMaybe, isJust, listToMaybe)

import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM


-- TODO: Optimize me!!!!
coalesceAASTGs :: AASTG api c -> AASTG api c -> AASTG api c
coalesceAASTGs a1 a2 = autoCoalesce lb start
  where
    lb  = maxNodeID a1'
    a1' = normalizeNodes 0        a1
    a2' = normalizeNodes (lb + 1) a2
    start = directCoalesceState 0 (lb + 1) $
      AASTG 0 (getEdgesFrom a1' <> getEdgesFrom a2') (getEdgesTo a1' <> getEdgesTo a2')

directCoalesceState :: NodeID -> NodeID -> AASTG api c -> AASTG api c
directCoalesceState er ee aastg@(AASTG s fs bs) = AASTG 0 fs' bs'
  where
    fs' = HM.map (map (renameNodesInEdge (IM.singleton ee er))) . HM.delete ee . HM.adjust (<> edgesFrom ee aastg) er $ fs
    bs' = edgesTo2EdgesFrom fs

autoCoalesce :: NodeID               -- Largest node id in the black group
             -> AASTG api c
             -> AASTG api c
autoCoalesce lb aastg = case listToMaybe [(b', b, r) | b <- blacks, r <- reds, let b' = b ~<=~ r, let r' = r ~<=~ b, b' || r'] of
  Nothing                         -> aastg
  Just (bIsSub, b, r) | bIsSub    -> autoCoalesce lb (directCoalesceState r b aastg)
                      | otherwise -> autoCoalesce lb (directCoalesceState b r aastg)
  where
    (blacks, reds) = partition (<= lb) (allNodes aastg)
    pathMap        = getPathMap aastg
    paths          = concat $ HM.elems pathMap
    deps           = HM.fromList [(path, pathDeps         path) | path <- paths]
    degs           = HM.fromList [(path, pathDegradedDeps path) | path <- paths]
    calls          = HM.fromList [(path, pathCalls        path) | path <- paths]
    (~<=~)         = upperSubNode pathMap (deps HM.!) (degs HM.!) (calls HM.!)

upperSubNode :: NodePathMap api c
             -> (APath api c -> DependenceMap)     -- DependenceMap getter
             -> (APath api c -> DegradedDepMap)    -- DegradedDependenceMap getter
             -> (APath api c -> [Edge api c])      -- api call sequence getter
             -> NodeID
             -> NodeID
             -> Bool
upperSubNode ctx deps degs calls n1 n2 = and [or [isJust $ p1 ~<=~ p2 | p2 <- getPaths n2] | p1 <- getPaths n1]
  where
    (~<=~) = effectiveSubpath deps degs calls
    getPaths n = HM.lookupDefault [] n ctx


