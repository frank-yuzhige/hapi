{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE BangPatterns #-}

module Test.HAPI.AASTG.Analysis.GenRule where
import Test.HAPI.AASTG.Analysis.ProcType (ProcType, UnboundedProcTypeMap (coerce2Bounded), isSubType', (!*), boundProcType, edge2Act)
import Test.HAPI.AASTG.Core (AASTG (..), NodeID, edgesFrom2EdgesTo, allNodes, Edge, startNode, endNode, allEdges, singletonAASTG, addEdge, changeEdgeNode, edgesFrom, isEquivalentEdge, isUpdateEdge, isRedirEdge)
import Test.HAPI.Effect.Eff (Alg, debug)
import Test.HAPI.AASTG.Analysis.Rename (VarSubstitution, renameVars, maxNodeID, unifyVarSubstitution, renameVarsInEdge)
import Test.HAPI.AASTG.Analysis.Add (addSubgraph)
import Test.HAPI.AASTG.Analysis.Nodes (childGraph)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Hashable (Hashable (..))
import Test.HAPI.AASTG.Analysis.TypeCheck (TypedAASTG (castAASTG, typeCheckCtx), procTypeUBOf, procCtxOf, TypeCheckCtx (procTypes, procCtxs), typeCheckEither, checkEdge)
import Control.Monad (filterM)
import Data.HashSet (HashSet)
import Test.HAPI.Api (ApiName)
import Text.Printf (printf)


data GenRule api c = GenRule
  { rulePre          :: ProcType
  , ruleGen          :: Edge api c
  , rulePost         :: ProcType
  , genRuleUBTypeMap :: UnboundedProcTypeMap
  }
  deriving (Eq, Show)


genRule4Edge :: Edge api c -> TypedAASTG api c -> GenRule api c
genRule4Edge edge aastg = GenRule ts edge te uptm
  where
    (s, e) = (startNode edge, endNode edge)
    uptm   = procTypes $ typeCheckCtx aastg
    ts     = procTypeUBOf s aastg
    te     = procTypeUBOf e aastg

genRules4AASTG :: TypedAASTG api c -> [GenRule api c]
genRules4AASTG aastg = map (`genRule4Edge` aastg) (allEdges $ castAASTG aastg)

ruleApplicable :: (Alg sig m, ApiName api)
               => NodeID
               -> GenRule api c
               -> TypedAASTG api c
               -> m [(NodeID, VarSubstitution)]
ruleApplicable i rule@(GenRule pre gen post uptm) aastg = do
  mv <- boundProcType uptm pre `isSubType'` boundProcType uptm2 ti
  case mv of
    Nothing  -> do
      -- debug $ printf "%s: pre failed on %s! \n %s \n %s" (show 'ruleApplicable) (show i) (show (boundProcType uptm pre)) (show (boundProcType uptm2 ti))
      return []
    Just vsb -> do
      let edge' = renameVarsInEdge vsb gen
      if any (isEquivalentEdge edge') (edgesFrom i (castAASTG aastg)) then return [] else do
        merr <- checkEdge (procCtxOf i aastg) edge'
        case merr of
          Just tec -> do
            -- debug $ printf "%s: ctx failed on %s!" (show 'ruleApplicable) (show i)
            return []
          Nothing  -> do
            -- debug $ printf "%s: pre SAT!" (show 'ruleApplicable)
            xs <- concat <$> traverse (checkPost vsb edge') (allNodes $ castAASTG aastg)
            if isRedirEdge gen
              then return xs
              else return $ (maxNodeID (castAASTG aastg) + 1, vsb) : xs
  where
    ti = procTypeUBOf i aastg
    uptm2 = procTypes $ typeCheckCtx aastg
    checkPost vsb e' j = do
      mv <- boundProcType uptm post `isSubType'` boundProcType uptm2 (edge2Act e' $ procTypeUBOf j aastg)
      case mv >>= unifyVarSubstitution vsb of
        Nothing   -> return []
        Just vsb' -> return [(j, vsb')]

applyRuleOn ::
             ( Alg sig m
             , ApiName api)
            => (NodeID, NodeID)
            -> VarSubstitution
            -> GenRule api c
            -> TypedAASTG api c
            -> m (Maybe (TypedAASTG api c))
applyRuleOn (s, e) vsb (GenRule _ edge _ _) ta = do
  t <- typeCheckEither aastg'
  case t of
    Left !tce  -> do
      debug $ printf "%s: tce = %s" (show 'applyRuleOn) (show tce)
      return Nothing
    Right ta' -> return (Just ta')
  where
    aastg  = castAASTG ta
    aastg' = addEdge (changeEdgeNode s e $ renameVarsInEdge vsb edge) aastg


data GenRuleUB api c = GenRuleUB { grGiveUB :: ProcType, grDerive :: AASTG api c }
  deriving (Eq, Show)

ruleApplicableUB :: Alg sig m => (GenRuleUB api c, UnboundedProcTypeMap) -> (ProcType, UnboundedProcTypeMap) -> m (Maybe VarSubstitution)
ruleApplicableUB (GenRuleUB t _, uptm1) (t', uptm2) = t1 `isSubType'` t2
  where
    t1 = boundProcType uptm1 t
    t2 = boundProcType uptm2 t'

unsafeApplyRule :: GenRuleUB api c -> NodeID -> VarSubstitution -> AASTG api c -> AASTG api c
unsafeApplyRule (GenRuleUB _ a) i vsb = addSubgraph i (renameVars vsb a)

genRuleForNode :: NodeID -> UnboundedProcTypeMap -> AASTG api c -> GenRuleUB api c
genRuleForNode i uptm aastg = GenRuleUB (uptm !* i) (AASTG i derive (edgesFrom2EdgesTo derive))
  where
    derive = childGraph i aastg

genRulesForAASTG :: UnboundedProcTypeMap -> AASTG api c -> [GenRuleUB api c]
genRulesForAASTG uptm aastg = [genRuleForNode k uptm aastg | k <- allNodes aastg]

instance Hashable (GenRuleUB api c) where
  hashWithSalt salt (GenRuleUB given derive) = salt
    `hashWithSalt` given
    `hashWithSalt` derive


instance Hashable (GenRule api c) where
  hashWithSalt salt (GenRule pre gen post uptm) = (salt
    `hashWithSalt` pre
    `hashWithSalt` gen
    `hashWithSalt` post)
    `hashIntMap` coerce2Bounded uptm
    where
      hashIntMap salt im = salt `hashWithSalt` IM.toAscList im
