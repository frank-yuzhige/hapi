{-# LANGUAGE ExplicitNamespaces #-}
module Test.HAPI.AASTG.Analysis.SubPath where
import Test.HAPI.AASTG.Analysis.Path (pathCalls, pathEndNode, Path)
import Test.HAPI.AASTG.Analysis.Dependence (pathDeps, lookupNode, VarSubstitution, getUnificationFromArgs, unifyVarSubstitution, applyVarSubstitution, pathDegradedDeps, isSubNodeDependence)
import Test.HAPI.AASTG.Core (Edge (APICall))
import qualified Data.TypeRepMap as TM
import Test.HAPI.Api (apiEqProofs)
import Data.Type.Equality (castWith, apply, type (:~:) (Refl))

-- TODO
{-
A path p1 is an effective subpath of p2, iff.
  1. The sequence of API calls in p1 & p2 are the same.
  2. There exists a variable substitution s.t. the dependence before each API call in P1 & P2 are the same.
  3. Under the said variable substitution in 2, the dependence at the end nodes in p1 is a subset of p2.
-}
-- |
effectiveSubpath :: Path p => p api c -> p api c -> Maybe ()
effectiveSubpath p1 p2 = do
  sub <- findVarSub c1 c2
  let nde2' = applyVarSubstitution sub nde2
  g <- isSubNodeDependence nde1 nde2'
  return ()
  where
    d1   = pathDeps  p1
    d2   = pathDeps  p2
    d1'  = pathDegradedDeps p1
    d2'  = pathDegradedDeps p2
    c1   = pathCalls p1
    c2   = pathCalls p2
    nde1 = lookupNode (pathEndNode p1) d1'
    nde2 = lookupNode (pathEndNode p2) d2'
    findVarSub :: [Edge api c] -> [Edge api c] -> Maybe VarSubstitution
    findVarSub [] [] = Just TM.empty
    findVarSub (APICall s1 e1 _ api1 args1 : c1) (APICall s2 e2 _ api2 args2 : c2) = do
      (_, proof, _) <- api1 `apiEqProofs` api2
      u             <- getUnificationFromArgs nd1 nd2 (castWith (apply Refl proof) args1) args2
      u'            <- findVarSub c1 c2
      unifyVarSubstitution u u'
      where
        nd1 = lookupNode s1 d1
        nd2 = lookupNode s2 d2
    findVarSub _ _ = Nothing
