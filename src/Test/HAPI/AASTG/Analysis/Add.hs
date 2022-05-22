module Test.HAPI.AASTG.Analysis.Add where
import Test.HAPI.AASTG.Core (AASTG (..), allNodes, NodeID, startNode, edgesFrom2EdgesTo)
import Test.HAPI.AASTG.Analysis.Rename (maxNodeID, renameNodes)
import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM
import Data.Containers.ListUtils (nubIntOn)
import Data.Hashable (hash)

addSubgraph :: NodeID -> AASTG api c -> AASTG api c -> AASTG api c
addSubgraph n sub parent = AASTG (getStart parent) fs (edgesFrom2EdgesTo fs)
  where
    ns   = (getStart sub, n) : [i | i <- allNodes sub, i /= getStart sub] `zip` [maxNodeID parent + 1 ..]
    sub' = renameNodes (IM.fromList ns) sub
    fs   = IM.filter (not . null)
         $ IM.map (nubIntOn hash)
         $ IM.unionWith (<>) (getEdgesFrom sub') (getEdgesFrom parent)
