{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.HAPI.AASTG.Analysis.PathExtra where

import Test.HAPI.Api (apiEqProofs)
import Test.HAPI.AASTG.Analysis.Path (pathCalls, pathEndNode, Path, APathView (APathView), outPaths, APath (APath), slice)
import Test.HAPI.AASTG.Analysis.Dependence (pathDeps, lookupNode, VarSubstitution, getUnificationFromArgs, unifyVarSubstitution, applyVarSubstitution, pathDegradedDeps, isSubNodeDependence, DependenceMap, DegradedDepMap)
import Test.HAPI.AASTG.Core (Edge (APICall), AASTG (AASTG, getStart), NodeID)
import Test.HAPI.AASTG.Effect.Trav (TravHandler(TravHandler), TravEvent (OnEdge, OnNode), runTrav, travPath)


import Control.Monad (when)
import Control.Algebra (Has, type (:+:), run)
import Control.Effect.State (State, gets, modify, get, put)
import Data.Type.Equality (castWith, apply, type (:~:) (Refl))
import Data.Map (Map)

import qualified Data.Map as M
import qualified Data.HashSet as HS
import qualified Data.TypeRepMap as TM
import Control.Carrier.State.Church (runState)
import Data.HashSet (HashSet)


type NodePathMap  api c = Map NodeID [APath api c]
type NodePathMap' api c = Map NodeID (HashSet (APath api c))

-- TODO
{-
A path p1 is an effective subpath of p2, iff.
  1. The sequence of API calls in p1 & p2 are the same.
  2. There exists a variable substitution s.t. the dependence before each API call in P1 & P2 are the same.
  3. Under the said variable substitution in 2, the dependence at the end nodes in p1 is a subset of p2.
-}
-- |
effectiveSubpath :: Path p
                 => (p api c -> DependenceMap)     -- DependenceMap getter
                 -> (p api c -> DegradedDepMap)    -- DegradedDependenceMap getter
                 -> (p api c -> [Edge api c])      -- api call sequence getter
                 -> p api c                        -- p1
                 -> p api c                        -- p2
                 -> Maybe ()
effectiveSubpath dep deg calls p1 p2 = do
  sub <- findVarSub c1 c2
  let nde2' = applyVarSubstitution sub nde2
  g <- isSubNodeDependence nde1 nde2'
  return ()
  where
    d1   = dep   p1
    d2   = dep   p2
    d1'  = deg   p1
    d2'  = deg   p2
    c1   = calls p1
    c2   = calls p2
    nde1 = lookupNode (pathEndNode p1) d1'
    nde2 = lookupNode (pathEndNode p2) d2'
    findVarSub :: [Edge api c] -> [Edge api c] -> Maybe VarSubstitution
    findVarSub [] [] = Just TM.empty
    findVarSub (APICall s1 e1 _ api1 args1 : c1) (APICall s2 e2 _ api2 args2 : c2) = do
      (_, proof, _) <- api1 `apiEqProofs` api2
      u             <- getUnificationFromArgs nd1 nd2 (castWith (apply Refl proof) args1) args2
      u'            <- findVarSub c1 c2
      unifyVarSubstitution u u'
      where
        nd1 = lookupNode s1 d1
        nd2 = lookupNode s2 d2
    findVarSub _ _ = Nothing


getPathMap :: forall api c. AASTG api c -> NodePathMap api c
getPathMap aastg = M.map HS.toList $ M.unionsWith (<>) (map trav paths)
  where
    paths = outPaths (getStart aastg) aastg
    trav p = run
      . runState @Int (\s m -> return m) 0
      . runState @(NodePathMap' api c) (\s _ -> return s) M.empty
      . runTrav (handler p)
      $ travPath p

    handler :: forall sig m. Has (State Int :+: State (NodePathMap' api c)) sig m
            => APath api c -> TravHandler api c m
    handler path = TravHandler $ \case
      OnEdge e -> return ()
      OnNode n -> do
        missing <- gets @(NodePathMap' api c) (M.notMember n)
        when missing $ modify @(NodePathMap' api c) (M.insert n HS.empty)
        i <- get @Int
        when (i > 0) $ modify (M.adjust (HS.insert (slice 0 i path)) n)
        modify @Int (+ 1)
