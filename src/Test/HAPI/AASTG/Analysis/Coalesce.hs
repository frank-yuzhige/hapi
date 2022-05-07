{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Test.HAPI.AASTG.Analysis.Coalesce where

import Test.HAPI.AASTG.Core (AASTG (AASTG, getEdgesFrom, getEdgesTo, getStart), NodeID, Edge (Update, Forget, Assert, APICall), allNodes, edgesFrom, edgesTo2EdgesFrom, startNode, edgesFrom2EdgesTo, endNode)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes, maxNodeID, renameNodesInEdge, VarSubstitution, emptyVarSub, renameNodesViaOffset, renameVars, isIdempotentVarSub)
import Test.HAPI.AASTG.Analysis.PathExtra (NodePathMap, effectiveSubpath, getIncomingPathsMap, findForkParent)
import Test.HAPI.AASTG.Analysis.Dependence (pathDeps, pathDegradedDeps, DependenceMap, DegradedDepMap, unifyVarSubstitution)
import Test.HAPI.AASTG.Analysis.Path (Path(pathCalls, pathEndNode), APath)
import Data.List ( partition, (\\), sortBy )
import Data.IntMap (IntMap)
import Data.Maybe (fromMaybe, isJust, listToMaybe)

import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM
import Data.Containers.ListUtils (nubIntOn)
import Data.Hashable (Hashable(hash))
import Test.HAPI.AASTG.Analysis.Nodes (unrelatedNodeMap, nodeDepthMap, childrenNodes)
import Test.HAPI.Effect.Eff (Alg, debug, run, Eff, debugIO)
import Text.Printf (printf)
import Test.HAPI.AASTG.GraphViz (prettyAASTG, previewAASTG)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Monad (foldM, forM)
import Data.Function (on)
import qualified Data.IntSet as IS
import Test.HAPI.Util.Empty (liftMaybe)
import qualified Data.TypeRepMap as TM
import qualified Data.HashMap.Strict as HS

-- TODO: Optimize me!!!!
-- | Coalesce 2 AASTGs
coalesceAASTG :: Alg sig m => Int -> AASTG api c -> AASTG api c -> m ([(NodeID, NodeID)], AASTG api c)
coalesceAASTG n a1 a2 = do
  let p = coalescePreprocess a1 a2
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceAASTG: After preprocess: \n%s" (prettyAASTG p)
  -- debugIO $ previewAASTG p
  autoCoalesce n p


coalesceAASTGs ::  Alg sig m => Int -> [AASTG api c] -> m (AASTG api c)
coalesceAASTGs n = \case
  []     -> error "Empty list of AASTGs to coalesce"
  [a]    -> return a
  a : as -> do
    x      <- coalesceAASTGs n as
    (_, r) <- coalesceAASTG  n a  x
    return r

-- | TODO: Children will fight, fix me! (fork children on var substitution)
directCoalesceState :: NodeID -> NodeID -> AASTG api c -> AASTG api c
directCoalesceState er ee aastg@(AASTG s fs bs) = AASTG 0 fs' bs'
  where
    fs' = IM.map (nubIntOn hash . map (renameNodesInEdge (IM.singleton ee er)))
        . IM.delete ee
        . IM.adjust (<> edgesFrom ee aastg) er
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
  let aastg'' = normalizeNodes 0 aastg'
  case record of
    Nothing -> return ([], aastg'')
    Just p  -> do
      (history, ans) <- autoCoalesce (maxStep - 1) aastg''
      return (p : history, ans)

-- FIXME
directCoalesceNode :: Alg sig m
                   => NodeID
                   -> APath api c
                   -> VarSubstitution
                   -> AASTG api c
                   -> m (AASTG api c)
directCoalesceNode er p vsb aastg@(AASTG s fs bs) = do
    -- debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.directCoalesceNode: coalescing [%d <- %d]" er ee
    -- debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.directCoalesceNode: children = %s" (show children)
    -- debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.directCoalesceNode: ee' = %d" ee'
    let ans = directCoalesceState er ee' combine
    return ans
    where
      ee  = pathEndNode p
      ee' = maxNodeID aastg + 1
      -- | Delete from the original graph, the subgraph from the last parent node with only 1 outgoing edge.
      fs' = case findForkParent p aastg of
        Nothing -> foldr IM.delete fs (childrenOf ee)
        Just ed -> IM.adjust (filter (/= ed)) (startNode ed)
                 $ foldr IM.delete fs (childrenOf (endNode ed))
      subgraph = let f = childGraph ee aastg
                 in  renameVars vsb
                  .  normalizeNodes ee'
                  $  AASTG ee f (edgesFrom2EdgesTo f)
      childrenOf = IS.toList . (childrenNodes aastg IM.!)
      froms      = IM.filter (not . null) (fs' <> getEdgesFrom subgraph)
      combine    = AASTG s froms (edgesFrom2EdgesTo froms)

coalesceOneStep :: Alg sig m
                => AASTG api c
                -> m (Maybe (NodeID, NodeID), AASTG api c)
coalesceOneStep aastg = do
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: depths = %s" (show nodeDepths)
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: allNodes = %s" (show (allNodes aastg))
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: num of paths = %d" (length paths)
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: candidates count = %d" (length candidates)
  -- debugIO $ previewAASTG aastg
  go candidates
  where
    go []           = return (Nothing, aastg)
    go ((b, r): xs) = do
      -- debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: checking: %s" (show (b, r))
      r' <- r ~<=~ b
      case r' of
        Just vsb -> do
          ans <- directCoalesceNode b (singlePathOf r) vsb aastg
          return (Just (b, r), ans)
        Nothing  -> do
          b' <- b ~<=~ r
          case b' of
            Just vsb -> do
              ans <- directCoalesceNode r (singlePathOf b) vsb aastg
              return (Just (r, b), ans)
            Nothing  -> go xs

    nodeDepths     = nodeDepthMap        aastg
    candidateMap   = unrelatedNodeMap    aastg
    ipaths         = getIncomingPathsMap aastg
    paths          = concat $ HM.elems ipaths
    deps           = HM.fromList [(path, pathDeps         path) | path <- paths]
    degs           = HM.fromList [(path, pathDegradedDeps path) | path <- paths]
    calls          = HM.fromList [(path, pathCalls        path) | path <- paths]
    (~<=~)         = upperSubNode ipaths (deps HM.!) (degs HM.!) (calls HM.!)
    singlePathOf   = head . (ipaths HM.!)
    candidates     = [(b, r) | b <- sortBy (compare `on` (nodeDepths IM.!)) (allNodes aastg)
                             , r <- sortBy (compare `on` (nodeDepths IM.!)) (candidateMap IM.! b)
                             ]

upperSubNode :: Alg sig m
             => NodePathMap api c                  -- All paths went through each node
             -> (APath api c -> DependenceMap)     -- DependenceMap getter
             -> (APath api c -> DegradedDepMap)    -- DegradedDependenceMap getter
             -> (APath api c -> [Edge api c])      -- api call sequence getter
             -> NodeID
             -> NodeID
             -> m (Maybe VarSubstitution)
upperSubNode ipaths deps degs calls n1 n2 = case ps1 of
  [p1] -> go p1 ps2
  _    -> do
    debug $ printf "%s: Node %d has multiple incoming paths, skipping..." (show 'upperSubNode) n1
    return Nothing  -- Multiple incoming node forbidden
  where
    go p1 [] = return Nothing
    go p1 (p2 : ps2) = do
      mv <- p1 ~<=~ p2
      case mv of
        Nothing  -> go p1 ps2
        Just vsb -> return (Just vsb)

    a ~<=~ b   = runEmpty (return Nothing) (return . Just) (effectiveSubpath deps degs calls a b)
    pathsTo n  = HM.lookupDefault [] n ipaths
    (ps1, ps2) = (pathsTo n1, pathsTo n2)


childGraph :: NodeID -> AASTG api c -> IntMap [Edge api c]
childGraph n aastg = IM.fromList [(c, edgesFrom c aastg) | c <- IS.toList $ childrenNodes aastg IM.! n]
