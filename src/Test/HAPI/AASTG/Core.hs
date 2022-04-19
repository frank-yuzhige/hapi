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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.HAPI.AASTG.Core where
import Test.HAPI.Effect.QVS (QVS (QVS), attributes2QVSs, qvs2m)
import Test.HAPI.Api (ApiDefinition, ApiName (apiName), apiEq)
import Test.HAPI.Args (Args, showArgs, Attribute (Get), attributesEq, repEq, showAttributes)
import Test.HAPI.PState (PKey (PKey, getPKeyID), PState (PState), PStateSupports (record, forget))
import Test.HAPI.Common (Fuzzable)
import Data.SOP (All, NP)
import Data.Kind (Type)
import Data.HList (HList (HCons, HNil), hMap, typeRep)
import Data.List (groupBy, intercalate)
import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Serialize (Serialize)
import Type.Reflection (Typeable)
import Data.SOP.Constraint (Compose)
import Data.Containers.ListUtils (nubInt)
import Data.Hashable (Hashable (hashWithSalt))

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM


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
  APICall :: forall a sig api p c. (Fuzzable a, IsValidCall c api p)
          => NodeID             -- From
          -> NodeID             -- To
          -> Maybe (PKey a)     -- Store result to variable
          -> api p a            -- API call (constructor)
          -> NP Attribute p     -- Argument Attributes List
          -> Edge api c

type IsValidCall c api p = (All c p, All (Compose Eq Attribute) p, ApiName api, All Fuzzable p, Typeable p)

data AASTG sig c = AASTG {
  getStart     :: !NodeID,
  getEdgesFrom :: !(HashMap NodeID [Edge sig c]),
  getEdgesTo   :: !(HashMap NodeID [Edge sig c])
} deriving Eq

data TaggedEdge t api c = TE { getTag :: t, getEdge :: Edge api c }

newAASTG :: [Edge sig c] -> AASTG sig c
newAASTG es = AASTG 0 (groupEdgesOn startNode es) (groupEdgesOn endNode es)

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
edgesFrom i (AASTG _ f _) = fromMaybe [] (f HM.!? i)

edgesTo :: NodeID -> AASTG api c -> [Edge api c]
edgesTo i (AASTG _ _ b) = fromMaybe [] (b HM.!? i)

allNodes :: AASTG api c -> [NodeID]
allNodes (AASTG start fs bs) = nubInt (start : HM.keys fs <> HM.keys bs)

allEdges :: AASTG api c -> [Edge api c]
allEdges = concatMap snd . HM.toList . getEdgesFrom

groupEdgesOn :: (Edge sig c -> NodeID) -> [Edge sig c] -> HashMap NodeID [Edge sig c]
groupEdgesOn f = HM.fromListWith (<>)
               . fmap (\e -> (f e, [e]))

edgesFrom2EdgesTo :: HashMap NodeID [Edge sig c] -> HashMap NodeID [Edge sig c]
edgesFrom2EdgesTo = groupEdgesOn startNode . concat . HM.elems

edgesTo2EdgesFrom :: HashMap NodeID [Edge sig c] -> HashMap NodeID [Edge sig c]
edgesTo2EdgesFrom = groupEdgesOn endNode . concat . HM.elems

showEdgeLabel :: Edge api c -> String
showEdgeLabel = \case
  Update  s e k  a        -> "update " <> getPKeyID k <> " = " <> show a
  Forget  s e k           -> "forget " <> getPKeyID k
  Assert  s e x  y        -> "assert " <> getPKeyID x <> " = " <> show y
  APICall s e mx api args -> "call "   <> maybe "" ((<> " = ") . getPKeyID) mx <> apiName api <> "(" <> intercalate ", " (showAttributes args) <> ")"

-- | Instances
instance Show (Edge api c) where
  show e = wrap $ header (startNode e) (endNode e) <> showEdgeLabel e
    where
      header s e = show s <> " -> " <> show e <> ": "
      wrap n     = "<" <> n <> ">"

instance Eq (Edge api c) where
  Update s e k a == Update s' e' k' a' =
    s == s' && e == e' && repEq k k' && repEq a a'
  Assert s e x y == Assert s' e' x' y' =
    s == s' && e == e' && repEq x x' && repEq y y'
  APICall s e mx api args == APICall s' e' mx' api' args' =
    s == s' && e == e' && repEq mx mx' && apiEq api api' && attributesEq args args'
  _ == _ = False

instance Hashable (Edge api c) where
  hashWithSalt salt (Update s e k a) = salt
    `hashWithSalt` "u"
    `hashWithSalt` s
    `hashWithSalt` e
    `hashWithSalt` k
    `hashWithSalt` a
  hashWithSalt salt (Forget  s e x) = salt
    `hashWithSalt` "f"
    `hashWithSalt` s
    `hashWithSalt` e
    `hashWithSalt` x
  hashWithSalt salt (Assert  s e x y) = salt
    `hashWithSalt` "a"
    `hashWithSalt` s
    `hashWithSalt` e
    `hashWithSalt` x
    `hashWithSalt` y
  hashWithSalt salt (APICall s e mx api args) = salt
    `hashWithSalt` "c"
    `hashWithSalt` s
    `hashWithSalt` e
    `hashWithSalt` mx
    `hashWithSalt` apiName api
    `hashWithSalt` args

deriving instance Show (AASTG api c)
