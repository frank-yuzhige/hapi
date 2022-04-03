{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Test.HAPI.AASTG.Core where
import Test.HAPI.Effect.QVS (QVS (QVS), Attribute (Get, Anything), attributes2QVSs, qvs2m)
import GHC.TypeNats (Nat)
import Data.Kind (Type)
import Data.HList (HList (HCons, HNil), hMap)
import Test.HAPI.Api (ApiDefinition, ApiName)
import Test.HAPI.Effect.Api(Api, mkCall)
import Control.Effect.Sum (Member, Members)
import Control.Algebra (Has, Algebra, type (:+:), send)
import Test.HAPI.Args (Args)
import Test.HAPI.PState (PKey (PKey), PState (PState), PStateSupports (record))
import Test.HAPI.Common (Fuzzable)
import Control.Effect.State (State, modify)
import Data.SOP (All, NP)
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.List (groupBy)
import Data.Function (on)
import Control.Effect.Error (throwError, Error)
import Test.HAPI.Effect.Property (shouldBe, PropertyA)
import Data.Maybe (fromMaybe)

-- Abstract API state transition graph

type NodeID = Int

data Edge sig c where
  Update  :: forall c a sig. (Fuzzable a, c a)
          => NodeID            -- From
          -> NodeID            -- To
          -> PKey a            -- Variable
          -> Attribute a       -- Attribute of the value
          -> Edge sig c
  -- TODO better assertion
  Assert  :: forall c a sig. (Fuzzable a, c a, Eq a)
          => NodeID            -- From
          -> NodeID            -- To
          -> PKey a            -- Variable x
          -> PKey a            -- Variable y
          -> Edge sig c
  APICall :: forall c a sig p. (Fuzzable a, All c p, ApiName sig, All Show p)
          => NodeID             -- From
          -> NodeID             -- To
          -> Maybe (PKey a)     -- Store result to variable
          -> sig p a            -- API call (constructor)
          -> NP Attribute p     -- Argument Attributes List
          -> Edge sig c

data AASTG sig c = AASTG {
  getStart :: NodeID,
  getEdges :: [Edge sig c]
}

startNode :: Edge api c -> NodeID
startNode (Update s _ _ _) = s
startNode (Assert s _ _ _) = s
startNode (APICall s _ _ _ _) = s

endNode :: Edge api c -> NodeID
endNode (Update _ e _ _) = e
endNode (Assert _ e _ _) = e
endNode (APICall _ e _ _ _) = e

edgesFrom :: NodeID -> AASTG api c -> [Edge api c]
edgesFrom i (AASTG _ es) = filter ((== i) . startNode) es

edgesTo :: NodeID -> AASTG api c -> [Edge api c]
edgesTo i (AASTG _ es) = filter ((== i) . endNode) es

groupEdges :: [Edge sig c] -> Map NodeID [Edge sig c]
groupEdges = M.fromList
           . fmap (\es -> (startNode (head es), es))
           . groupBy ((==) `on` startNode)

-- | Synthesize fuzzer stubs
synthStub :: forall api sig c m. (Has (Api api :+: QVS c :+: State PState :+: PropertyA) sig m) => AASTG api c -> [m ()]
synthStub aastg@(AASTG start edges) = synth start
  where
    emap    = groupEdges edges
    synth i = case emap M.!? i of
      Nothing -> [return ()]
      Just es -> concat [(synthOneStep edge >>) <$> synth (endNode edge) | edge <- es]
    synthOneStep :: Edge api c -> m ()
    synthOneStep (Update s e k a) = do
      v <- send (QVS @c a)
      modify @PState (record k v)
    synthOneStep (Assert s e x y) = do
      x' <- send (QVS @c (Get x))
      y' <- send (QVS @c (Get y))
      x' `shouldBe` y'
    synthOneStep (APICall s e mx api args) = do
      -- 1. Resolve Attributes (Into QVS)
      args <- qvs2m @c (attributes2QVSs args)
      -- 2. Make APICall using qvs
      r <- mkCall api args
      -- 3. Store return value in state
      case mx of
        Nothing -> return ()
        Just k  -> modify @PState (record k r)

