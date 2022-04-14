{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
module Test.HAPI.AASTG.Analysis.Path where

import Test.HAPI.AASTG.Core (Edge (APICall), NodeID, AASTG (AASTG), endNode, edgesFrom, startNode, edgesTo)

import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import Data.DList (DList)
import Data.Set (Set)
import Data.IntSet (IntSet)

import qualified Data.Map    as M
import qualified Data.Vector as V
import qualified Data.DList  as D
import qualified Data.Set    as S
import qualified Data.IntSet as IS
import Text.Printf (printf)


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

data APath api c = APath { getPathEdges :: Vector (Edge api c), getPathNodes :: IntSet }

aPath :: Vector (Edge api c) -> APath api c
aPath v = APath v (IS.fromList $ map endNode (V.toList v))

outPaths :: NodeID -> AASTG api c -> [APath api c]
outPaths i aastg = map (aPath . V.fromList . D.toList) (gen i)
  where
    gen n = case edgesFrom n aastg of
      [] -> [D.empty]
      es -> concat [D.cons e <$> gen (endNode e) | e <- es]

inPaths :: NodeID -> AASTG api c -> [APath api c]
inPaths i aastg = map (aPath . V.fromList . D.toList) (gen i)
  where
    gen n = case edgesTo n aastg of
      [] -> [D.empty]
      es -> concat [D.cons e <$> gen (startNode e) | e <- es]


-- | A "view" of the path from the start
data APathView api c = APathView { getAPath :: APath api c, getViewLength :: Int }




instance Path APath where
  pathStartNode (APath p _)   = startNode $ V.head p
  pathEndNode   (APath p _)   = endNode   $ V.last p
  pathAsList    (APath p _)   = V.toList p
  pathEdgeAt    (APath p _) i = p V.! i


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

