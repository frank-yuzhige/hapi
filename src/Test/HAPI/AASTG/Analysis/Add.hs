module Test.HAPI.AASTG.Analysis.Add where
import Test.HAPI.AASTG.Core (AASTG (..), allNodes, NodeID, startNode, edgesFrom2EdgesTo)
import Test.HAPI.AASTG.Analysis.Rename (maxNodeID, renameNodes)
import qualified Data.IntMap as IM
import qualified Data.HashMap.Strict as HM

addSubgraph :: NodeID -> AASTG api c -> AASTG api c -> AASTG api c
addSubgraph n sub parent = AASTG (getStart parent) fs (edgesFrom2EdgesTo fs)
  where
    ns   = (n, n) : [i | i <- allNodes sub, i /= n] `zip` [maxNodeID parent + 1 ..]
    sub' = renameNodes (IM.fromList ns) parent
    fs   = IM.unionWith (<>) (getEdgesFrom sub') (getEdgesFrom parent)
