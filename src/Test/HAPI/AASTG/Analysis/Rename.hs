{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# LANGUAGE DeriveGeneric #-}


module Test.HAPI.AASTG.Analysis.Rename where

import Test.HAPI.AASTG.Core (AASTG (AASTG), NodeID, Edge (..), allNodes)
import Data.IntMap (IntMap)
import Data.Maybe (fromMaybe, fromJust)
import Data.TypeRepMap (TypeRepMap)
import Test.HAPI.PState (PKey (PKey))
import Test.HAPI.Common (Fuzzable)

import qualified Data.IntMap.Strict  as IM
import qualified Data.TypeRepMap     as TM
import qualified Data.HashMap.Strict as HM
import Test.HAPI.Args (Attribute (..), Attributes, DirectAttribute (..))
import Data.SOP.NP (NP(Nil, (:*)))
import qualified Test.HAPI.Util.TypeRepMap as TM
import Data.Data (typeRep, Data, Typeable)
import GHC.Generics
import Data.Hashable (Hashable)
import qualified Data.HashSet as HS

type NodeRenameMap = IntMap NodeID  -- NodeID -> NodeID

type VarSubstitution = TypeRepMap SubEntry

newtype SubEntry t = SE { unSE :: HM.HashMap (PKey t) (PKey t) }
  deriving (Eq, Show, Ord, Generic)

newtype SubEntry' t = SE' { unSE' :: HM.HashMap (PKey t) (HS.HashSet (PKey t)) }

instance Hashable (SubEntry t) where

-- Node Sub

maxNodeID :: AASTG api c -> NodeID
maxNodeID (AASTG start fs bs) = maximum (start : IM.keys fs <> IM.keys bs)

minNodeID :: AASTG api c -> NodeID
minNodeID (AASTG start fs bs) = minimum (start : IM.keys fs <> IM.keys bs)

renameNodes :: NodeRenameMap -> AASTG api c -> AASTG api c
renameNodes nrm aastg@(AASTG start fs bs) = AASTG (nrm IM.! start) (renameNodesInMap nrm fs) (renameNodesInMap nrm bs)

renameNodesInMap :: NodeRenameMap -> IntMap [Edge api c] -> IntMap [Edge api c]
renameNodesInMap nrm = IM.mapKeys (nrm IM.!) . IM.map (renameNodesInEdge nrm <$>)

renameNodesInEdge :: NodeRenameMap -> Edge api c -> Edge api c
renameNodesInEdge nrm = \case
  Update   s e k a          -> Update   (look s) (look e) k a
  Forget   s e k            -> Forget   (look s) (look e) k
  Assert   s e x y          -> Assert   (look s) (look e) x y
  APICall  s e mx api args  -> APICall  (look s) (look e) mx api args
  Redirect s e              -> Redirect (look s) (look e)
  where
    look i = fromMaybe i $ nrm IM.!? i

renameNodesViaOffset :: Int -> AASTG api c -> AASTG api c
renameNodesViaOffset offset aastg = renameNodes (IM.fromList [(n, n + offset) | n <- allNodes aastg]) aastg

normalizeNodes :: Int -> AASTG api c -> AASTG api c
normalizeNodes offset aastg = renameNodes (IM.fromList (allNodes aastg `zip` [offset..])) aastg

-- Var Sub

emptyVarSub :: VarSubstitution
emptyVarSub = TM.empty

singletonVarSub :: forall t. Typeable t => PKey t -> PKey t -> VarSubstitution
singletonVarSub k v = TM.insert (SE $ HM.singleton k v) emptyVarSub

lookVar :: forall t. (Fuzzable t) => PKey t -> VarSubstitution -> Maybe (PKey t)  -- NoMonoLocalBinds
lookVar k vsb = do
  SE se <- TM.lookup @t vsb
  HM.lookup k se

lookVar' :: forall t. (Fuzzable t) => PKey t -> VarSubstitution -> PKey t -- NoMonoLocalBinds
lookVar' k vsb = fromMaybe k (lookVar k vsb) -- error $ "Test.HAPI.AASTG.Analysis.Rename.lookVar': variable " <> show k <> " not present"

isIdempotentVarSub :: VarSubstitution -> Bool
isIdempotentVarSub vsb = and $ TM.toListWith (\(SE se) -> HM.foldrWithKey (\k v n -> k == v && n) True se) vsb

-- | Unify 2 variable substitutions
-- Unification fails when a variable is assigned to 2 different variables in 2 subs.
unifyVarSubstitution :: VarSubstitution -> VarSubstitution -> Maybe VarSubstitution
unifyVarSubstitution vs1 vs2 = TM.hoistA unliftSE merge
  where
    -- Need to use helper SE' since @TM.unionWith@ only works for @f x -> f x -> f x@
    vs1'  = TM.hoist liftSE vs1
    vs2'  = TM.hoist liftSE vs2
    merge = TM.unionWith (\a b -> SE' $ HM.unionWith HS.union (unSE' a) (unSE' b)) vs1' vs2'

-- | Lift a SubEntry to SubEntry', where it is a key -> Set of key mapping
liftSE :: SubEntry t -> SubEntry' t
liftSE = SE' . HM.map HS.singleton . unSE

-- | Unlift a SubEntry' to SubEntry. If the SubEntry' contains a one-to-many mapping, then unlift fails.
unliftSE :: SubEntry' t -> Maybe (SubEntry t)
unliftSE (SE' se) = SE <$> HM.foldrWithKey folder (Just HM.empty) se
  where
    folder k s e
      | HS.size s == 1 = HM.insert k (head $ HS.toList s) <$> e
      | otherwise     = Nothing

renameVars :: VarSubstitution -> AASTG api c -> AASTG api c
renameVars vsb aastg@(AASTG start fs bs) = AASTG start (renameVarsInMap vsb fs) (renameVarsInMap vsb bs)

renameVarsInMap :: VarSubstitution -> IntMap [Edge api c] -> IntMap [Edge api c]
renameVarsInMap vsb = IM.map (renameVarsInEdge vsb <$>)

renameVarsInEdge :: VarSubstitution -> Edge api c -> Edge api c
renameVarsInEdge vsb = \case
  Update   s e k a        -> Update   s e (look k) a
  Forget   s e k          -> Forget   s e (look k)
  Assert   s e x y        -> Assert   s e (look x) (look y)
  APICall  s e x api args -> APICall  s e  (look x) api (renameVarsInAttrs vsb args)
  Redirect s e            -> Redirect s e
  where
    look k = lookVar' k vsb

renameVarsInAttr :: VarSubstitution -> Attribute t -> Attribute t
renameVarsInAttr vsb = \case
  Direct (Get k) -> Direct (Get (lookVar' k vsb))
  AnyOf xs       -> AnyOf (map (renameVarsInAttr vsb) xs)
  other          -> other

renameVarsInAttrs :: VarSubstitution -> Attributes t -> Attributes t
renameVarsInAttrs _   Nil       = Nil
renameVarsInAttrs vsb (a :* as) = renameVarsInAttr vsb a :* renameVarsInAttrs vsb as

