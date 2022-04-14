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
{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Core where
import Test.HAPI.Effect.QVS (QVS (QVS), attributes2QVSs, qvs2m)
import GHC.TypeNats (Nat)
import Data.Kind (Type)
import Data.HList (HList (HCons, HNil), hMap, typeRep)
import Test.HAPI.Api (ApiDefinition, ApiName (apiName), apiEq)
import Test.HAPI.Effect.Api(Api, mkCall)
import Control.Effect.Sum (Member, Members)
import Control.Algebra (Has, Algebra, type (:+:), send)
import Test.HAPI.Args (Args, showArgs, Attribute (Get), attributesEq, repEq)
import Test.HAPI.PState (PKey (PKey), PState (PState), PStateSupports (record, forget))
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
import Data.Serialize (Serialize)
import Type.Reflection (Typeable)
import Data.SOP.Constraint (Compose)
import Data.Containers.ListUtils (nubInt)

-- Abstract API state transition graph

type NodeID = Int
type EdgeID = Int

data Edge api c where
  Update  :: forall a api c. (Fuzzable a, c a)
          => NodeID            -- From
          -> NodeID            -- To
          -> PKey a            -- Variable
          -> Attribute a       -- Attribute of the value
          -> Edge api c
  Forget  :: forall a api c. (Fuzzable a, c a)
          => NodeID            -- From
          -> NodeID            -- To
          -> PKey a            -- Variable
          -> Edge api c
  -- TODO better assertion
  Assert  :: forall a api c. (Fuzzable a, c a, Eq a)
          => NodeID            -- From
          -> NodeID            -- To
          -> PKey a            -- Variable x
          -> PKey a            -- Variable y
          -> Edge api c
  APICall :: forall a sig api p c. (Fuzzable a, All c p, All (Compose Eq Attribute) p, ApiName api, All Fuzzable p, Typeable p)
          => NodeID             -- From
          -> NodeID             -- To
          -> Maybe (PKey a)     -- Store result to variable
          -> api p a            -- API call (constructor)
          -> NP Attribute p     -- Argument Attributes List
          -> Edge api c

data AASTG sig c = AASTG {
  getStart     :: !NodeID,
  getEdgesFrom :: !(Map NodeID [Edge sig c]),
  getEdgesTo   :: !(Map NodeID [Edge sig c])
} deriving Eq

data TaggedEdge t api c = TE { getTag :: t, getEdge :: Edge api c }

newAASTG :: [Edge sig c] -> AASTG sig c
newAASTG es = AASTG 0 (groupEdgesOn startNode es) (groupEdgesOn endNode es)
  where
    groupEdgesOn f = M.fromList
                   . fmap (\es -> (f (head es), es))
                   . groupBy ((==) `on` f)

startNode :: Edge api c -> NodeID
startNode (Update s _ _ _) = s
startNode (Forget s _ _)   = s
startNode (Assert s _ _ _) = s
startNode (APICall s _ _ _ _) = s

endNode :: Edge api c -> NodeID
endNode (Update _ e _ _) = e
endNode (Forget _ e _)   = e
endNode (Assert _ e _ _) = e
endNode (APICall _ e _ _ _) = e

edgesFrom :: NodeID -> AASTG api c -> [Edge api c]
edgesFrom i (AASTG _ f _) = fromMaybe [] (f M.!? i)

edgesTo :: NodeID -> AASTG api c -> [Edge api c]
edgesTo i (AASTG _ _ b) = fromMaybe [] (b M.!? i)

allNodes :: AASTG api c -> [NodeID]
allNodes (AASTG start fs bs) = nubInt (start : M.keys fs <> M.keys bs)

allEdges :: AASTG api c -> [Edge api c]
allEdges = concatMap snd . M.toList . getEdgesFrom

groupEdgesOn :: (Edge sig c -> NodeID) -> [Edge sig c] -> Map NodeID [Edge sig c]
groupEdgesOn f = M.fromList
               . fmap (\es -> (f (head es), es))
               . groupBy ((==) `on` f)

edgesFrom2EdgesTo :: Map NodeID [Edge sig c] -> Map NodeID [Edge sig c]
edgesFrom2EdgesTo = groupEdgesOn startNode . concat . M.elems

edgesTo2EdgesFrom :: Map NodeID [Edge sig c] -> Map NodeID [Edge sig c]
edgesTo2EdgesFrom = groupEdgesOn endNode . concat . M.elems

-- | Synthesize fuzzer stubs
synthStub :: forall api sig c m. (Has (Api api :+: QVS c :+: State PState :+: PropertyA) sig m) => AASTG api c -> [m ()]
synthStub (AASTG start edges _) = synth start
  where
    synth i = case edges M.!? i of
      Nothing -> [return ()]
      Just es -> concat [(synthOneStep edge >>) <$> synth (endNode edge) | edge <- es]
    synthOneStep :: Edge api c -> m ()
    synthOneStep (Update s e k a) = do
      v <- send (QVS @c a)
      modify @PState (record k v)
    synthOneStep (Forget s e k) = do
      modify @PState (forget k)
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

-- | Instances
instance Show (Edge api c) where
  show = \case
    Update  s e k  a        -> header s e <> "update " <> show k <> " = " <> show a
    Forget  s e k           -> header s e <> "forget " <> show k
    Assert  s e x  y        -> header s e <> "assert " <> show x <> " = " <> show y
    APICall s e mx api args -> header s e <> apiName api <> "(" <> "..." <> ")" <> maybe "" ((" -> " <>) . show) mx
    where
      header s e = show s <> " -> " <> show e <> ": "

instance Eq (Edge api c) where
  Update s e k a == Update s' e' k' a' =
    s == s' && e == e' && repEq k k' && repEq a a'
  Assert s e x y == Assert s' e' x' y' =
    s == s' && e == e' && repEq x x' && repEq y y'
  APICall s e mx api args == APICall s' e' mx' api' args' =
    s == s' && e == e' && repEq mx mx' && apiEq api api' && attributesEq args args'
  _ == _ = False
