{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
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
import Test.HAPI.Effect.QVS (QVS (..), attributes2QVSs, qvs2m)
import Test.HAPI.Api (ApiDefinition, ApiName (apiName, showApiFromPat), apiEq)
import Test.HAPI.Args (Args, Attribute (..), attributesEq, repEq, attrs2Pat, DirectAttribute)
import Test.HAPI.PState (PKey (PKey, getPKeyID), PState (PState), PStateSupports (record, forget))
import Test.HAPI.Common (Fuzzable)
import Data.SOP (All, NP)
import Data.Kind (Type)
import Data.HList (HList (HCons, HNil), hMap, typeRep)
import Data.List (groupBy, intercalate, sort)
import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Serialize (Serialize)
import Type.Reflection (Typeable)
import Data.SOP.Constraint (Compose)
import Data.Containers.ListUtils (nubInt, nubIntOn)
import Data.Hashable (Hashable (hashWithSalt), hash)

import Data.HashMap.Strict (HashMap)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IM


-- Abstract API state transition graph

type NodeID = Int
type EdgeID = Int

data Edge apis c where
  -- | Updates the value of a variable by the given attribute
  Update   :: forall a api c. (Fuzzable a, c a)
           => NodeID            -- From
           -> NodeID            -- To
           -> PKey a            -- Variable
           -> Attribute a       -- Attribute of the value
           -> Edge api c
  ContIf   :: forall a api c. (Fuzzable Bool, c Bool)  -- TODO: Not yet supported
           => NodeID            -- From
           -> NodeID            -- To
           -> DirectAttribute Bool
           -> Edge api c
  -- TODO better assertion
  Assert   :: forall a api c. (Fuzzable Bool, c Bool)
           => NodeID               -- From
           -> NodeID               -- To
           -> DirectAttribute Bool
           -> Edge api c
  APICall  :: forall a sig api p c. (Fuzzable a, c a, IsValidCall c api p)
           => NodeID             -- From
           -> NodeID             -- To
           -> PKey a             -- Store result to variable
           -> api p a            -- API call (constructor)
           -> NP Attribute p     -- Argument Attributes List
           -> Edge api c

  -- | For internal use only
  Redirect :: ()
           => NodeID             -- From
           -> NodeID             -- To
           -> Edge api c

type IsValidCall c api p = (All c p, All (Compose Eq Attribute) p, ApiName api, All Fuzzable p, Typeable p)

data AASTG sig c = AASTG {
  getStart     :: !NodeID,
  getEdgesFrom :: !(IntMap [Edge sig c]),
  getEdgesTo   ::   IntMap [Edge sig c]
} deriving Eq

data TaggedEdge t api c = TE { getTag :: t, getEdge :: Edge api c }

newAASTG :: [Edge sig c] -> AASTG sig c
newAASTG es = AASTG 0 (groupEdgesOn startNode es) (groupEdgesOn endNode es)

singletonAASTG :: Edge sig c -> AASTG sig c
singletonAASTG e = AASTG (startNode e) (groupEdgesOn startNode [e]) (groupEdgesOn endNode [e])

startNode :: Edge api c -> NodeID
startNode (Update s _ _ _) = s
startNode (ContIf s _ _)   = s
startNode (Assert s _ _) = s
startNode (APICall s _ _ _ _) = s
startNode (Redirect s _ ) = s

endNode :: Edge api c -> NodeID
endNode (Update _ e _ _) = e
endNode (ContIf _ e _)   = e
endNode (Assert _ e _) = e
endNode (APICall _ e _ _ _) = e
endNode (Redirect _ e) = e

getTerminators :: AASTG api c -> [NodeID]
getTerminators aastg = [ n | n <- allNodes aastg, null (edgesFrom n aastg) ]

edgesFrom :: NodeID -> AASTG api c -> [Edge api c]
edgesFrom i (AASTG _ f _) = fromMaybe [] (f IM.!? i)

edgesTo :: NodeID -> AASTG api c -> [Edge api c]
edgesTo i (AASTG _ _ b) = fromMaybe [] (b IM.!? i)

allNodes :: AASTG api c -> [NodeID]
allNodes (AASTG start fs bs) = nubInt (start : IM.keys fs <> IM.keys bs)

allEdges :: AASTG api c -> [Edge api c]
allEdges = concat . IM.elems . getEdgesFrom

groupEdgesOn :: (Edge sig c -> NodeID) -> [Edge sig c] -> IntMap [Edge sig c]
groupEdgesOn f = IM.fromListWith (<>)
               . fmap (\e -> (f e, [e]))

edgesFrom2EdgesTo :: IntMap [Edge sig c] -> IntMap [Edge sig c]
edgesFrom2EdgesTo = groupEdgesOn endNode . concat . IM.elems

edgesTo2EdgesFrom :: IntMap [Edge sig c] -> IntMap [Edge sig c]
edgesTo2EdgesFrom = groupEdgesOn startNode . concat . IM.elems

changeEdgeNode :: NodeID -> NodeID -> Edge api c -> Edge api c
changeEdgeNode i j = \case
  Update   _ _ k  a        -> Update   i j k  a
  ContIf   _ _ k           -> ContIf   i j k
  Assert   _ _ p           -> Assert   i j p
  APICall  _ _ mx api args -> APICall  i j mx api args
  Redirect _ _             -> Redirect i j

showEdgeLabel :: Edge api c -> String
showEdgeLabel = \case
  Update   s e k  a        -> "update " <> getPKeyID k <> " = " <> show a
  ContIf   s e p           -> "if "     <> show p
  Assert   s e p           -> "assert " <> show p
  APICall  s e mx api args -> ""        <> getPKeyID mx <> " = " <> showApiFromPat api (attrs2Pat args) -- apiName api <> "(" <> intercalate ", " (showAttributes args) <> ")"
  Redirect s e             -> "redir"

addEdge :: Edge api c -> AASTG api c -> AASTG api c
addEdge e aastg = AASTG (getStart aastg)
                        (IM.unionWith (\a b -> nubIntOn hash (a <> b)) (IM.singleton (startNode e) [e]) (getEdgesFrom aastg))
                        (IM.unionWith (\a b -> nubIntOn hash (a <> b)) (IM.singleton (endNode   e) [e]) (getEdgesTo aastg))

isEquivalentEdge :: Edge api c -> Edge api c -> Bool
isEquivalentEdge e e' = e == changeEdgeNode (startNode e) (endNode e) e'

isUpdateEdge :: Edge api c -> Bool
isUpdateEdge Update {} = True
isUpdateEdge _         = False

isRedirEdge :: Edge api c -> Bool
isRedirEdge Redirect {} = True
isRedirEdge _           = False

-- | Instances
instance Show (Edge api c) where
  show e = wrap $ header (startNode e) (endNode e) <> showEdgeLabel e
    where
      header s e = show s <> " -> " <> show e <> ": "
      wrap n     = "<" <> n <> ">"

instance Eq (Edge api c) where
  Update s e k a == Update s' e' k' a' =
    s == s' && e == e' && repEq k k' && repEq a a'
  Assert s e p == Assert s' e' p' =
    s == s' && e == e' && p == p'
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
  hashWithSalt salt (ContIf  s e x) = salt
    `hashWithSalt` "i"
    `hashWithSalt` s
    `hashWithSalt` e
    `hashWithSalt` x
  hashWithSalt salt (Assert  s e p) = salt
    `hashWithSalt` "a"
    `hashWithSalt` s
    `hashWithSalt` e
    `hashWithSalt` p
  hashWithSalt salt (APICall s e mx api args) = salt
    `hashWithSalt` "c"
    `hashWithSalt` s
    `hashWithSalt` e
    `hashWithSalt` mx
    `hashWithSalt` apiName api
    `hashWithSalt` args
  hashWithSalt salt (Redirect s e) = salt
    `hashWithSalt` "r"
    `hashWithSalt` s
    `hashWithSalt` e

deriving instance Show (AASTG api c)
instance Hashable (AASTG api c) where
  hashWithSalt salt (AASTG s f e) = salt
    `hashWithSalt` s
    `hashIntMap` f
    `hashIntMap` e
    where
      hashIntMap salt im = salt `hashWithSalt` IM.toList im
