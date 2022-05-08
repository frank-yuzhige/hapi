{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.HAPI.AASTG.Analysis.Coalesce where

import Test.HAPI.AASTG.Core (AASTG (AASTG, getEdgesFrom, getEdgesTo, getStart), NodeID, Edge (Update, Forget, Assert, APICall), allNodes, edgesFrom, edgesTo2EdgesFrom, startNode, edgesFrom2EdgesTo, endNode)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes, maxNodeID, renameNodesInEdge, VarSubstitution, emptyVarSub, renameNodesViaOffset, renameVars, isIdempotentVarSub, renameVarsInEdge)
import Test.HAPI.AASTG.Analysis.Dependence (pathDeps, pathDegradedDeps, DependenceMap, DegradedDepMap, applyVarSubstitution)
import Test.HAPI.AASTG.Analysis.Path (Path(pathCalls, pathEndNode), APath)
import Data.List ( partition, (\\), sortBy )
import Data.IntMap (IntMap)
import Data.Maybe (fromMaybe, isJust, listToMaybe)

import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM
import Data.Containers.ListUtils (nubIntOn)
import Data.Hashable (Hashable(hash))
import Test.HAPI.AASTG.Analysis.Nodes (unrelatedNodeMap, nodeDepthMap, childrenNodes, UnrelatedNodeMap)
import Test.HAPI.Effect.Eff (Alg, debug, run, Eff, debugIO)
import Text.Printf (printf)
import Test.HAPI.AASTG.GraphViz (prettyAASTG, previewAASTG)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Monad (foldM, forM, join, when)
import Data.Function (on)
import qualified Data.IntSet as IS
import Test.HAPI.Util.Empty (liftMaybe)
import qualified Data.TypeRepMap as TM
import qualified Data.HashMap.Strict as HS
import Test.HAPI.AASTG.Analysis.ProcType (ProcTypeMap, isSubType, inferProcType, emptySubTypeCtx)
import Control.Carrier.NonDet.Church (runNonDet)
import Control.Applicative (Applicative(liftA2))
import Test.HAPI.Api (ApiName)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR))
import qualified Control.Applicative as A
import Control.Carrier.State.Church (runState)

-- TODO: Optimize me!!!!
-- | Coalesce 2 AASTGs
coalesceAASTG ::
               ( Alg sig m
               , ApiName api) => Int -> AASTG api c -> AASTG api c -> m ([(NodeID, NodeID)], AASTG api c)
coalesceAASTG n a1 a2 = do
  let p = coalescePreprocess a1 a2
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceAASTG: After preprocess: \n%s" (prettyAASTG p)
  -- debugIO $ previewAASTG p
  autoCoalesce n p


coalesceAASTGs :: (Alg sig m, ApiName api) => Int -> [AASTG api c] -> m (AASTG api c)
coalesceAASTGs n = \case
  []     -> error "Empty list of AASTGs to coalesce"
  [a]    -> return a
  a : as -> do
    x      <- coalesceAASTGs n as
    (_, r) <- coalesceAASTG  n a  x
    return r

directCoalesceState :: NodeID -> NodeID -> AASTG api c -> AASTG api c
directCoalesceState er ee aastg@(AASTG s fs bs) = AASTG 0 fs' (edgesFrom2EdgesTo fs')
  where
    fs' = IM.map (nubIntOn hash . map (renameNodesInEdge (IM.singleton ee er)))
        . IM.delete ee
        . IM.unionWith (<>) (IM.singleton er (edgesFrom ee aastg))
        $ fs

coalescePreprocess :: AASTG api c -> AASTG api c -> AASTG api c
coalescePreprocess a1 a2 = directCoalesceState 0 (lb + 1) combine
  where
    a1'     = normalizeNodes 0        a1
    lb      = maxNodeID a1'
    a2'     = normalizeNodes (lb + 1) a2
    combine = AASTG 0 (getEdgesFrom a1' <> getEdgesFrom a2') (getEdgesTo a1' <> getEdgesTo a2')

autoCoalesce ::
              ( Alg sig m
              , ApiName api)
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
directCoalesceNode ::
                    ( Alg sig m )
                   => NodeID            -- er Node
                   -> NodeID            -- ee Node (er nodes and ee nodes need to be unrelated)
                   -> VarSubstitution   -- Variable substitution
                   -> UnrelatedNodeMap  -- Unrelated Node Map
                   -> AASTG api c       --
                   -> m (AASTG api c)   --
directCoalesceNode er ee vsb ur aastg@(AASTG s fs bs)
  | related er ee || related ee er
    = fatalError 'directCoalesceNode FATAL_ERROR $ printf "Node %d and %d are related!" er ee
  | isIdempotentVarSub vsb = do
    debug $ printf "%s: Idempotent var sub" (show 'directCoalesceNode)
    return $ directCoalesceState er ee aastg
  | otherwise = do
    -- debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.directCoalesceNode: coalescing [%d <- %d]" er ee
    -- debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.directCoalesceNode: children = %s" (show children)
    debug $ printf "%s: apply sub on biparted AASTG, coalesce %d <- %d" (show 'directCoalesceNode) er ee
    -- debug $ printf "%s: combine = %s" (show 'directCoalesceNode) (show combine)
    return $ directCoalesceState er ee combine
    where
      related a b = a `notElem` ur IM.! b
      froms       = IM.mapWithKey (\k e -> if k `elem` (ur IM.! ee) then e else map (renameVarsInEdge vsb) e) fs
      combine     = AASTG s froms (edgesFrom2EdgesTo froms)

coalesceOneStep ::
                 ( Alg sig m
                 , ApiName api)
                => AASTG api c
                -> m (Maybe (NodeID, NodeID), AASTG api c)
coalesceOneStep aastg = do
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: depths = %s" (show nodeDepths)
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: allNodes = %s" (show (allNodes aastg))
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: unrelated = %s" (show unrelatedMap)
  -- debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: num of paths = %d" (length paths)
  -- debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: candidates count = %d" (length candidates)
  -- debugIO $ previewAASTG aastg
  ptm <- inferProcType aastg
  go ptm candidates
  where
    go ptm []           = return (Nothing, aastg)
    go ptm ((b, r): xs) = do
      debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: checking: %s" (show (b, r))
      debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of b = %s" (show (ptm IM.! b))
      debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of r = %s" (show (ptm IM.! r))
      r' <- r ~<=~ b
      case r' of
        Just vsb -> do
          debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of er = %s" (show (ptm IM.! b))
          debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of ee = %s" (show (ptm IM.! r))
          ans <- directCoalesceNode b r vsb unrelatedMap aastg
          return (Just (b, r), ans)
        Nothing  -> do
          b' <- b ~<=~ r
          case b' of
            Just vsb -> do
              debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of er = %s" (show (ptm IM.! r))
              debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of ee = %s" (show (ptm IM.! b))
              ans <- directCoalesceNode r b vsb unrelatedMap aastg
              return (Just (r, b), ans)
            Nothing  -> go ptm xs
      where
        (~<=~) = upperSubNode ptm
    nodeDepths     = nodeDepthMap        aastg
    unrelatedMap   = unrelatedNodeMap    aastg
    candidates     = [(b, r) | b <- sortBy (compare `on` (nodeDepths IM.!)) (allNodes aastg)
                             , r <- sortBy (compare `on` (nodeDepths IM.!)) (unrelatedMap IM.! b)
                             ]

upperSubNode :: Alg sig m
             => ProcTypeMap
             -> NodeID
             -> NodeID
             -> m (Maybe VarSubstitution)
upperSubNode ptm n1 n2 = do
  ans <- runState (\s a -> return a) emptySubTypeCtx
       $ runNonDet (liftA2 (A.<|>)) (return . Just) (return Nothing)
       $ isSubType (ptm IM.! n1) (ptm IM.! n2)
  when (isJust ans) $ debug $ printf "%s: %d <= %d, %s" (show 'upperSubNode) n1 n2 (show ans)
  return ans


childGraph :: NodeID -> AASTG api c -> IntMap [Edge api c]
childGraph n aastg = IM.fromList [(c, edgesFrom c aastg) | c <- IS.toList $ childrenNodes aastg IM.! n]
