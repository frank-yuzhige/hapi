{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Test.HAPI.AASTG.GraphViz where
import Test.HAPI.AASTG.Core (AASTG(AASTG), NodeID, allNodes, allEdges, Edge (..), startNode, endNode, showEdgeLabel)
import Data.Graph.Inductive (Graph (mkGraph), LEdge, prettyPrint, Gr, Node, prettify)
import Data.GraphViz (DotGraph, nonClusteredParams, graphToDot, preview)

toGraph :: Graph g => AASTG api c -> g NodeID String
toGraph aastg = mkGraph ([(n, n) | n <- allNodes aastg]) (map genEdges $ allEdges aastg)
  where
    genEdges :: Edge api c -> LEdge String
    genEdges e = (startNode e, endNode e, "<" <> showEdgeLabel e <> ">")

prettyAASTG :: AASTG api c -> String
prettyAASTG = prettify . toGraph @Gr

previewAASTG :: AASTG api c -> IO ()
previewAASTG = preview . toGraph @Gr

aastg2GraphViz :: AASTG api c -> DotGraph Node
aastg2GraphViz = graphToDot nonClusteredParams . toGraph @Gr




