{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.AASTG.Analysis.PathExtra where

import Test.HAPI.Api (apiEqProofs)
import Test.HAPI.AASTG.Analysis.Path (pathCalls, pathEndNode, Path (pathAsList), APathView (APathView), outPaths, APath (APath), slice)
import Test.HAPI.AASTG.Analysis.Dependence (pathDeps, lookupNode, getUnificationFromArgs, unifyVarSubstitution, applyVarSubstitution, pathDegradedDeps, isSubNodeDependence, DependenceMap, DegradedDepMap, showDegDep)
import Test.HAPI.AASTG.Core (Edge (APICall), AASTG (AASTG, getStart), NodeID, endNode, edgesFrom, startNode)
import Test.HAPI.AASTG.Effect.Trav (TravHandler(TravHandler), TravEvent (OnEdge, OnNode), runTrav, travPath)


import Control.Monad (when)
import Control.Algebra (Has, type (:+:), run)
import Control.Effect.State (State, gets, modify, get, put)
import Data.Type.Equality (castWith, apply, type (:~:) (Refl))
import Data.Map (Map)

import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.TypeRepMap as TM
import Control.Carrier.State.Church (runState)
import Data.HashSet (HashSet)
import Data.HashMap.Strict (HashMap)
import Test.HAPI.Effect.Eff
import Control.Carrier.Fail.Either (Fail)
import Control.Effect.Error (Error)
import Control.Effect.Empty ( Empty, empty )
import Text.Printf (printf)
import Test.HAPI.Util.Empty (liftMaybe)
import Test.HAPI.AASTG.Analysis.Rename (VarSubstitution)


type NodePathMap  api c = HashMap NodeID [APath api c]
type NodePathMap' api c = HashMap NodeID (HashSet (APath api c))

-- TODO
{-
A path p1 is an effective subpath of p2, iff.
  1. The sequence of API calls in p1 & p2 are the same.
  2. There exists a variable substitution s.t. the dependence before each API call in P1 & P2 are the same.
  3. Under the said variable substitution in 2, the dependence at the end nodes in p1 is a subset of p2.
-}
-- |
effectiveSubpath :: forall p sig m api c.
                    (Path p, Eff Empty sig m)
                 => (p api c -> DependenceMap)     -- DependenceMap getter
                 -> (p api c -> DegradedDepMap)    -- DegradedDependenceMap getter
                 -> (p api c -> [Edge api c])      -- API call sequence getter
                 -> p api c                        -- p1
                 -> p api c                        -- p2
                 -> m VarSubstitution
effectiveSubpath dep deg calls p1 p2 = do
  vsb <- findVarSub c1 c2
  debug $ printf "Test.HAPI.AASTG.Analysis.PathExtra.effectiveSubpath: Found var substitution: %s" (show vsb)
  let nde2' = applyVarSubstitution vsb nde2
  debug $ printf "Test.HAPI.AASTG.Analysis.PathExtra.effectiveSubpath: Degraded deps: %s, %s" (showDegDep nde1) (showDegDep nde2')
  g <- isSubNodeDependence nde1 nde2'
  debug $ printf "Test.HAPI.AASTG.Analysis.PathExtra.effectiveSubpath: Found final unification: %s" g
  return vsb
  where
    d1   = dep   p1
    d2   = dep   p2
    d1'  = deg   p1
    d2'  = deg   p2
    c1   = calls p1
    c2   = calls p2
    nde1 = lookupNode (pathEndNode p1) d1'
    nde2 = lookupNode (pathEndNode p2) d2'

    -- | Find the relevant variable substitution that unifies 2 API call sequence.
    findVarSub :: [Edge api c] -> [Edge api c] -> m VarSubstitution
    findVarSub [] [] = return TM.empty
    findVarSub (APICall s1 e1 _ api1 args1 : c1) (APICall s2 e2 _ api2 args2 : c2) = do
      (_, proof, _) <- liftMaybe $ api1 `apiEqProofs` api2
      u             <- liftMaybe $ getUnificationFromArgs nd1 nd2 (castWith (apply Refl proof) args1) args2
      u'            <- findVarSub c1 c2
      liftMaybe $ unifyVarSubstitution u u'
      where
        nd1 = lookupNode s1 d1
        nd2 = lookupNode s2 d2
    findVarSub _ _ = empty @sig

checkEffectiveSubpath :: forall p sig m api c.
                         (Path p, Eff Empty sig m)
                      => (p api c -> DegradedDepMap)    -- DegradedDependenceMap getter
                      -> VarSubstitution                -- Global variable substitution
                      -> p api c                        -- p1
                      -> p api c                        -- p2
                      -> m ()
checkEffectiveSubpath deg vsb p1 p2 = do
  let nde2' = applyVarSubstitution vsb nde2
  debug $ printf "Test.HAPI.AASTG.Analysis.PathExtra.checkEffectiveSubpath: Degraded deps: %s, %s" (showDegDep nde1) (showDegDep nde2')
  g <- isSubNodeDependence nde1 nde2'
  debug $ printf "Test.HAPI.AASTG.Analysis.PathExtra.checkEffectiveSubpath: Found final unification: %s" g
  where
    nde1 = lookupNode (pathEndNode p1) (deg p1)
    nde2 = lookupNode (pathEndNode p2) (deg p2)



getIncomingPathsMap :: forall api c. AASTG api c -> NodePathMap api c
getIncomingPathsMap aastg = HM.map HS.toList $ foldr (HM.unionWith (<>) . trav) HM.empty paths
  where
    paths = outPaths (getStart aastg) aastg
    trav p = run
      . runState @Int (\s m -> return m) 0
      . runState @(NodePathMap' api c) (\s _ -> return s) HM.empty
      . runTrav (handler p)
      $ travPath p

    handler :: forall sig m. Has (State Int :+: State (NodePathMap' api c)) sig m
            => APath api c -> TravHandler api c m
    handler path = TravHandler $ \case
      OnEdge e -> return ()
      OnNode n -> do
        missing <- gets @(NodePathMap' api c) (not . HM.member n)
        when missing $ modify @(NodePathMap' api c) (HM.insert n HS.empty)
        i <- get @Int
        when (i > 0) $ modify (HM.adjust (HS.insert (slice 0 i path)) n)
        modify @Int (+ 1)


findForkParent :: Path p => p api c -> AASTG api c -> Maybe (Edge api c)
findForkParent p aastg = visit $ reverse $ pathAsList p
  where
    visit []       = Nothing
    visit (e : es) = case edgesFrom (startNode e) aastg of
      [_] -> visit es
      _   -> Just  e
