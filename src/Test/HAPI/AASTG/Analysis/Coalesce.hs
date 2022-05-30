{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

module Test.HAPI.AASTG.Analysis.Coalesce where

import Test.HAPI.AASTG.Core (AASTG (AASTG, getEdgesFrom, getEdgesTo, getStart), NodeID, Edge (..), allNodes, edgesFrom, edgesTo2EdgesFrom, startNode, edgesFrom2EdgesTo, endNode)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes, maxNodeID, renameNodesInEdge, VarSubstitution, emptyVarSub, renameNodesViaOffset, renameVars, isIdempotentVarSub, renameVarsInEdge)
import Test.HAPI.AASTG.Analysis.Path (Path(pathCalls, pathEndNode), APath)
import Data.List ( partition, (\\), sortBy )
import Data.IntMap (IntMap)
import Data.Maybe (fromMaybe, isJust, listToMaybe, fromJust)

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
import Test.HAPI.AASTG.Analysis.ProcType (ProcTypeMap, isSubType, inferProcType, emptySubTypeCtx, UnboundedProcTypeMap, isSubTypeUB, inferProcTypeUB, (!*))
import Control.Carrier.NonDet.Church (runNonDet)
import Control.Applicative (Applicative(liftA2))
import Test.HAPI.Api (ApiName)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR))
import qualified Control.Applicative as A
import Control.Carrier.State.Church (runState)
import Test.HAPI.AASTG.Analysis.GenRule (GenRuleUB, ruleApplicableUB, unsafeApplyRule, genRulesForAASTG, GenRule (genRuleUBTypeMap), ruleApplicable, genRules4AASTG, applyRuleOn)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Test.HAPI.AASTG.Analysis.TypeCheck (TypedAASTG(..), TypeCheckCtx (procTypes))
import Data.Data (Typeable)

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
  []         -> error "Empty list of AASTGs to coalesce"
  [a]        -> return a
  a : b : as -> do
    (_, r) <- coalesceAASTG n a b
    coalesceAASTGs n (r : as)

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
             => Int
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
  ptm <- inferProcTypeUB aastg
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: ptm = %s" (show ptm)
  go ptm candidates
  where
    go ptm []           = return (Nothing, aastg)
    go ptm ((b, r): xs) = do
      debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: checking: %s" (show (b, r))
      debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of b = %s" (show (ptm !* b))
      debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of r = %s" (show (ptm !* r))
      r' <- r ~<=~ b
      case r' of
        Just vsb -> do
          debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of er = %s" (show (ptm !* b))
          debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of ee = %s" (show (ptm !* r))
          ans <- directCoalesceNode b r vsb unrelatedMap aastg
          return (Just (b, r), ans)
        Nothing  -> do
          b' <- b ~<=~ r
          case b' of
            Just vsb -> do
              debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of er = %s" (show (ptm !* r))
              debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.coalesceOneStep: type of ee = %s" (show (ptm !* b))
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
             => UnboundedProcTypeMap
             -> NodeID
             -> NodeID
             -> m (Maybe VarSubstitution)
upperSubNode ptm n1 n2 = do
  ans <- runState (\s a -> return a) emptySubTypeCtx
       $ runNonDet (liftA2 (A.<|>)) (return . Just) (return Nothing)
       $ isSubTypeUB ptm (ptm !* n1) (ptm !* n2)
  when (isJust ans) $ debug $ printf "%s: %d <= %d, %s" (show 'upperSubNode) n1 n2 (show ans)
  return ans


coalesceRuleOneStep ::
                     ( Alg sig m
                     , ApiName api
                     , Typeable c)
                     => TypedAASTG api c
                     -> [GenRule api c]
                     -> m (Maybe (NodeID, GenRule api c, Int), TypedAASTG api c)
coalesceRuleOneStep ta rules = do
  -- debug $ printf "%s: start one step" (show 'coalesceRuleOneStep)
  -- debug $ printf "%s: aastg=%s" (show 'coalesceRuleOneStep) (show aastg)
  let uptm1 = procTypes $ typeCheckCtx ta
  -- debug $ printf "%s: uptm1=%s" (show 'coalesceRuleOneStep) (show uptm1)
  go candidates
  where
    aastg      = castAASTG ta
    nodeDepths = nodeDepthMap aastg
    candidates = [(b, r, i) | b <- sortBy (compare `on` (nodeDepths IM.!)) (allNodes aastg)
                            , (r, i) <- rules `zip` [0..]
                            ]

    go [] = return (Nothing, ta)
    go ((i, rule, ri) : xs) = do
      vsbs <- ruleApplicable i rule ta
      case vsbs of
        []           -> go xs
        ((j, s) : _) -> do
          x <- applyRuleOn (i, j) s rule ta
          -- debug $ printf "%s: i=%s, rule: %s" (show 'coalesceRuleOneStep) (show i) (show rule)
          -- debug $ printf "%s: x = %s" (show 'coalesceRuleOneStep) (show x)
          return (Just (i, rule, ri), fromJust x)
      -- forM vsbs $ \(j, vsb) -> do
      --   _
      -- case mvsb of
      --   Nothing  -> go uptm1 xs
      --   Just vsb -> do
      --     debug $ printf "%s: r <= t: %s" (show 'coalesceRuleOneStep) (show (r, t))
      --     let ans = unsafeApplyRule r x vsb aastg
      --     return (Just (x, r), ans)

autoCoalesceRule :: ( Alg sig m
                    , ApiName api
                    , Typeable c)
                    => Int
                    -> [GenRule api c]
                    -> TypedAASTG api c
                    -> m ([(NodeID, GenRule api c)], TypedAASTG api c)
autoCoalesceRule 0       _     aastg = return ([], aastg)
autoCoalesceRule maxStep rules aastg = do
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.autoCoalesceRule: rule count: %s" (show (length rules))
  (!record, !aastg') <- coalesceRuleOneStep aastg rules
  debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.autoCoalesceRule: coalesce %s" (show record)
  -- let !aastg'' = normalizeNodes 0 aastg'
  debugIO$ previewAASTG (castAASTG aastg')
  case record of
    Nothing -> return ([], aastg')
    Just (x, r, ri)  -> do
      -- debug $ printf "Test.HAPI.AASTG.Analysis.Coalesce.autoCoalesceRule: next rule count: %s" (show (remove ri rules))
      (history, ans) <- autoCoalesceRule (maxStep - 1) (remove ri rules) aastg'
      return ((x, r) : history, ans)
  where
    remove :: Int -> [a] -> [a]
    remove _ [] = []
    remove 0 (x:xs) = xs
    remove n (x:xs) = x : remove (n-1) (xs)


coalesceRuleAASTG ::
               ( Alg sig m
               , ApiName api
               , Typeable c) => Int -> TypedAASTG api c -> TypedAASTG api c -> m ([(NodeID, GenRule api c)], TypedAASTG api c)
coalesceRuleAASTG n a1 a2 = do
  autoCoalesceRule n (genRules4AASTG a2) a1

coalesceRuleAASTGs :: (Alg sig m, ApiName api, Typeable c) => Int -> [TypedAASTG api c] -> m (TypedAASTG api c)
coalesceRuleAASTGs n = \case
  []         -> error "Empty list of AASTGs to coalesce"
  [a]        -> return a
  a : b : as -> do
    (_, r) <- coalesceRuleAASTG n a b
    coalesceRuleAASTGs n (r : as)
