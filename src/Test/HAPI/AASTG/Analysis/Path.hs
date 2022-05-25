{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
module Test.HAPI.AASTG.Analysis.Path where

import Test.HAPI.AASTG.Core (Edge (APICall), NodeID, AASTG (AASTG, getStart), endNode, edgesFrom, startNode, edgesTo)

import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import Data.DList (DList)
import Data.Set (Set)
import Data.IntSet (IntSet)
import Text.Printf (printf)
import Data.Map (Map)

import qualified Data.Map    as M
import qualified Data.Vector as V
import qualified Data.DList  as D
import qualified Data.Set    as S
import qualified Data.IntSet as IS
import Control.Algebra (Has)
import Control.Effect.State (State)
import GHC.Generics (Generic)
import Data.Hashable (Hashable (hashWithSalt, hash))
import Data.Containers.ListUtils (nubIntOn)
import Data.Data (Typeable)


class Path p where
  pathStartNode   :: p api c -> NodeID
  pathEndNode     :: p api c -> NodeID
  pathAsList      :: p api c -> [Edge api c]
  pathEdgeAt      :: p api c -> Int -> Edge api c

  pathNodesInSeq  :: p api c -> [NodeID]
  pathNodesInSeq p = pathStartNode p : map endNode (pathAsList p)

  pathCallerNodes :: p api c -> [NodeID]
  pathCallerNodes = map startNode . filter (\case APICall {} -> True; _ -> False) . pathAsList

  pathCalls       :: p api c -> [Edge api c]
  pathCalls = filter (\case APICall {} -> True; _ -> False) . pathAsList


-- | A complete path
newtype APath api c = APath { getPathEdges :: Vector (Edge api c) }

slice :: Int -> Int -> APath api c -> APath api c
slice i n (APath p) = APath (V.slice i n p)
{-# INLINE slice #-}

outPaths :: NodeID -> AASTG api c -> [APath api c]
outPaths = outPaths' 20
{-# INLINE outPaths #-}

outPaths' :: Int -> NodeID -> AASTG api c -> [APath api c]
outPaths' c i aastg = nubIntOn hash $ map constrAPath (gen i c)
  where
    gen _ 0 = [D.empty]
    gen n c = case edgesFrom n aastg of
      [] -> [D.empty]
      es -> concat [D.cons e <$> gen (endNode e) (c - 1) | e <- es]

inPaths :: NodeID -> AASTG api c -> [APath api c]
inPaths = inPaths' 20
{-# INLINE inPaths #-}

inPaths' :: Int -> NodeID -> AASTG api c -> [APath api c]
inPaths' c i aastg = nubIntOn hash $ map constrAPath (gen i c)
  where
    gen _ 0 = [D.empty]
    gen n c = case edgesTo n aastg of
      [] -> [D.empty]
      es -> concat [D.cons e <$> gen (startNode e) (c - 1) | e <- es]


-- | APath Incremental Constructor
type APathConstr api c = DList (Edge api c)

constrAPath :: APathConstr api c -> APath api c
constrAPath = APath . V.fromList . D.toList

-- | A "view" of the path from the start
data APathView api c = APathView { getAPath :: APath api c, getViewLength :: Int }

instance Path APath where
  pathStartNode (APath p)   = startNode $ V.head p
  pathEndNode   (APath p)   = endNode   $ V.last p
  pathAsList    (APath p)   = V.toList p
  pathEdgeAt    (APath p) i = p V.! i

-- instance Hashable (APath api c) where
--   hashWithSalt s (APath p) = s
--     `hashWithSalt`

instance Path APathView where
  pathStartNode   (APathView p l) = pathStartNode p
  pathEndNode     (APathView p l)
    | l == 0    = pathStartNode p
    | otherwise = endNode $ getPathEdges p V.! (l - 1)

  pathNodesInSeq  (APathView p l)   = take (l + 1) (pathNodesInSeq p)
  pathAsList      (APathView p l)   = take l (pathAsList p)
  pathEdgeAt      (APathView p l) i
    | i < l     = pathEdgeAt p i
    | otherwise = error $ printf "APathView: Index %d >= length %d" i l


deriving instance Show    (APath api c)
deriving instance Typeable c => Eq      (APath api c)
deriving instance Generic (APath api c)
instance Hashable (APath api c) where
  hashWithSalt salt (APath p) = V.foldr (flip hashWithSalt) salt p

deriving instance Show (APathView api c)
deriving instance Typeable c => Eq   (APathView api c)
