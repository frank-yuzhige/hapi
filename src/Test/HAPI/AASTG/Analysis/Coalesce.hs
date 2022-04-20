{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.AASTG.Analysis.Coalesce where

import Test.HAPI.AASTG.Core (AASTG (AASTG, getEdgesFrom, getEdgesTo, getStart), NodeID, Edge (Update, Forget, Assert, APICall), allNodes, edgesFrom, edgesTo2EdgesFrom, startNode)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes, maxNodeID, renameNodesInEdge)
import Test.HAPI.AASTG.Analysis.PathExtra (NodePathMap, effectiveSubpath, getPathMap)
import Test.HAPI.AASTG.Analysis.Dependence (pathDeps, pathDegradedDeps, DependenceMap, DegradedDepMap)
import Test.HAPI.AASTG.Analysis.Path (Path(pathCalls), APath)
import Data.List ( partition, (\\), sortBy )
import Data.IntMap (IntMap)
import Data.Maybe (fromMaybe, isJust, listToMaybe)

import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM
import Data.Containers.ListUtils (nubIntOn)
import Data.Hashable (Hashable(hash))
import Test.HAPI.AASTG.Analysis.Nodes (unrelatedNodeMap, nodeDepthMap)
import Test.HAPI.Effect.Eff (Alg, debug, run)
import Text.Printf (printf)
import Test.HAPI.AASTG.GraphViz (prettyAASTG)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Monad (foldM)
import Data.Function (on)

-- TODO: Optimize me!!!!
-- | Coalesce 2 AASTGs
coalesceAASTG :: Alg sig m => Int -> AASTG api c -> AASTG api c -> m ([(NodeID, NodeID)], AASTG api c)
coalesceAASTG n a1 a2 = do
  let p = coalescePreprocess a1 a2
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceAASTG: After preprocess: \n%s" (prettyAASTG p)
  autoCoalesce n p

coalesceAASTGs ::  Alg sig m => Int -> [AASTG api c] -> m (AASTG api c)
coalesceAASTGs n = \case
  []     -> error "Empty list of AASTGs to coalesce"
  [a]    -> return a
  a : as -> do
    x <- coalesceAASTGs n as
    (_, r) <- coalesceAASTG n a x
    return r

-- | TODO: Children will fight, fix me! (fork children on var substitution)
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
    a1'     = normalizeNodes 0        a1
    lb      = maxNodeID a1'
    a2'     = normalizeNodes (lb + 1) a2
    combine = AASTG 0 (getEdgesFrom a1' <> getEdgesFrom a2') (getEdgesTo a1' <> getEdgesTo a2')

autoCoalesce :: Alg sig m
             => NodeID
             -> AASTG api c
             -> m ([(NodeID, NodeID)], AASTG api c)
autoCoalesce 0       aastg = return ([], aastg)
autoCoalesce maxStep aastg = do
  (record, aastg') <- coalesceOneStep aastg
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.autoCoalesce: coalesce %s" (show record)
  case record of
    Nothing -> return ([], aastg')
    Just p  -> do
      (history, ans) <- autoCoalesce (maxStep - 1) aastg'
      return (p : history, ans)


coalesceOneStep :: Alg sig m
                => AASTG api c
                -> m (Maybe (NodeID, NodeID), AASTG api c)
coalesceOneStep aastg = go [(b, r) | b <- sortBy (flip compare `on` (nodeDepths IM.!)) (allNodes aastg), r <- candidateMap IM.! b]
  where
    go []           = return (Nothing, aastg)
    go ((b, r): xs) = do
      r' <- r ~<=~ b
      if r' then return (Just (b, r), directCoalesceState b r aastg)
            else do
        b' <- b ~<=~ r
        if b' then return (Just (r, b), directCoalesceState r b aastg)
              else go xs

    nodeDepths     = nodeDepthMap aastg
    candidateMap   = unrelatedNodeMap aastg
    pathMap        = getPathMap aastg
    paths          = concat $ HM.elems pathMap
    deps           = HM.fromList [(path, pathDeps         path) | path <- paths]
    degs           = HM.fromList [(path, pathDegradedDeps path) | path <- paths]
    calls          = HM.fromList [(path, pathCalls        path) | path <- paths]
    (~<=~)         = upperSubNode pathMap (deps HM.!) (degs HM.!) (calls HM.!)

upperSubNode :: Alg sig m
             => NodePathMap api c                  -- All paths went through each node
             -> (APath api c -> DependenceMap)     -- DependenceMap getter
             -> (APath api c -> DegradedDepMap)    -- DegradedDependenceMap getter
             -> (APath api c -> [Edge api c])      -- api call sequence getter
             -> NodeID
             -> NodeID
             -> m Bool
upperSubNode ctx deps degs calls n1 n2
  = and <$> sequence [or <$> sequence [p1 ~<=~ p2 | p2 <- getPaths n2] | p1 <- getPaths n1]
  where
    a ~<=~ b = runEmpty (return False) (\_ -> return True) (effectiveSubpath deps degs calls a b)
    getPaths n = HM.lookupDefault [] n ctx


