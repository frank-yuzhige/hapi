{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Analysis.Coalesce where

import Test.HAPI.AASTG.Core (AASTG (AASTG, getEdgesFrom, getEdgesTo, getStart), NodeID, Edge (Update, Forget, Assert, APICall), allNodes, edgesFrom, edgesTo2EdgesFrom, startNode)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes, maxNodeID, renameNodesInEdge)
import Test.HAPI.AASTG.Analysis.PathExtra (NodePathMap, effectiveSubpath, getPathMap)
import Test.HAPI.AASTG.Analysis.Dependence (pathDeps, pathDegradedDeps, DependenceMap, DegradedDepMap)
import Test.HAPI.AASTG.Analysis.Path (Path(pathCalls), APath)
import Data.List ( partition, (\\) )
import Data.IntMap (IntMap)
import Data.Maybe (fromMaybe, isJust, listToMaybe)

import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM
import Data.Containers.ListUtils (nubIntOn)
import Data.Hashable (Hashable(hash))
import Test.HAPI.AASTG.Analysis.Nodes (unrelatedNodeMap)
import Test.HAPI.Effect.Eff (Alg)


-- TODO: Optimize me!!!!
coalesceAASTGs :: Alg sig m => Int -> AASTG api c -> AASTG api c -> m ([(NodeID, NodeID)], AASTG api c)
coalesceAASTGs n a1 a2 = autoCoalesce n (coalescePreprocess a1 a2)

directCoalesceState :: NodeID -> NodeID -> AASTG api c -> AASTG api c
directCoalesceState er ee aastg@(AASTG s fs bs) = AASTG 0 fs' bs'
  where
    fs' = HM.map (nubIntOn hash)
        . HM.map (map (renameNodesInEdge (IM.singleton ee er)))
        . HM.delete ee
        . HM.adjust (<> edgesFrom ee aastg) er
        $ fs
    bs' = edgesTo2EdgesFrom fs'

coalescePreprocess :: AASTG api c -> AASTG api c -> AASTG api c
coalescePreprocess a1 a2 = directCoalesceState 0 (lb + 1) combine
  where
    lb      = maxNodeID a1'
    a1'     = normalizeNodes 0        a1
    a2'     = normalizeNodes (lb + 1) a2
    combine = AASTG 0 (getEdgesFrom a1' <> getEdgesFrom a2') (getEdgesTo a1' <> getEdgesTo a2')

autoCoalesce :: Alg sig m
             => NodeID
             -> AASTG api c
             -> m ([(NodeID, NodeID)], AASTG api c)
autoCoalesce 0       aastg = return ([], aastg)
autoCoalesce maxStep aastg = do
  (record, aastg') <- coalesceOneStep aastg
  case record of
    Nothing -> return ([], aastg')
    Just p  -> do
      (history, ans) <- autoCoalesce (maxStep - 1) aastg'
      return (p : history, ans)


coalesceOneStep :: Alg sig m
                => AASTG api c
                -> m (Maybe (NodeID, NodeID), AASTG api c)
coalesceOneStep aastg = case listToMaybe [(r', b, r) | b <- allNodes aastg
                                                     , r <- candidateMap HM.! b
                                                     , let b' = b ~<=~ r
                                                     , let r' = r ~<=~ b
                                                     , b' || r'] of
  Nothing                         -> return (Nothing, aastg)
  Just (rIsSub, b, r) | rIsSub    -> return (Just (b, r), directCoalesceState b r aastg)
                      | otherwise -> return (Just (r, b), directCoalesceState r b aastg)
  where
    candidateMap   = unrelatedNodeMap aastg
    pathMap        = getPathMap aastg
    paths          = concat $ HM.elems pathMap
    deps           = HM.fromList [(path, pathDeps         path) | path <- paths]
    degs           = HM.fromList [(path, pathDegradedDeps path) | path <- paths]
    calls          = HM.fromList [(path, pathCalls        path) | path <- paths]
    (~<=~)         = upperSubNode pathMap (deps HM.!) (degs HM.!) (calls HM.!)

upperSubNode :: NodePathMap api c                  -- All paths went through each node
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


