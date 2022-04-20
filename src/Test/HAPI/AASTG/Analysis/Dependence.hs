{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.HAPI.AASTG.Analysis.Dependence where

import qualified Data.DList as D
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import qualified Data.IntMap as IM
import qualified Data.TypeRepMap as TM
import qualified Test.HAPI.Util.TypeRepMap as TM

import Data.TypeRepMap (TypeRepMap)
import Test.HAPI.PState (PKey (PKey))
import Data.IntMap (IntMap)
import Test.HAPI.AASTG.Core (AASTG (getStart), startNode, NodeID, Edge (Update, Forget, Assert, APICall), endNode)
import Test.HAPI.AASTG.Effect.Trav (TravHandler (TravHandler), TravEvent (OnEdge, OnNode), TravCA (runTravCA), travPath, runTrav)
import Control.Algebra (Has, run, type (:+:))
import Control.Carrier.State.Church (State, runState)
import Test.HAPI.Args (Attribute (Get, Value), showAttributes, eqAttributes)
import Control.Effect.State (gets, modify)
import Test.HAPI.AASTG.Analysis.Rename (maxNodeID, minNodeID)
import Data.Data (Typeable,type  (:~:) (Refl))
import Data.SOP (NP (Nil, (:*)), All)
import Test.HAPI.AASTG.Analysis.Path (pathNodesInSeq, Path)
import Test.HAPI.Api (apiEq, ApiName, apiEqProofs)
import Data.Type.Equality (testEquality, castWith, apply)
import Type.Reflection (typeOf)
import Test.HAPI.Common (Fuzzable)
import Data.Maybe (fromJust, isJust, fromMaybe)
import Data.Function (on)
import Data.List (intercalate)
import Control.Applicative (Const(getConst, Const), Applicative (liftA2))
import Control.Effect.Labelled (Labelled, runLabelled, sendLabelled, HasLabelled)
import Control.Effect.Fresh (Fresh (Fresh), fresh)
import Control.Carrier.Fresh.Church (runFresh)
import Data.Hashable (Hashable (hashWithSalt, hash))
import Test.HAPI.Effect.Eff (Eff, debug)
import Control.Effect.Empty (Empty, empty)
import Test.HAPI.Util.Empty (liftMaybe)
import Text.Printf (printf)

type DependenceMap' dep = IntMap (NodeDependence' dep)

type DependenceMap = DependenceMap' Dep

type DegradedDepMap = IntMap (TypeRepMap (DEntry' DegradedDep))

type NodeDependence' dep = TypeRepMap (DEntry' dep)

type NodeDependence = NodeDependence' Dep

type VarSubstitution = TypeRepMap SubEntry

type GroupCtx = TypeRepMap GroupEntry

type DEntry = DEntry' Dep

data Dep t where
  DepAttr ::                                              Attribute t               -> Dep t
  DepCall :: (ApiName api, Typeable p, All Fuzzable p) => api p t -> NP Attribute p -> Dep t

data DegradedDep t = DepAttr' (Attribute t) | DepCall' Int

-- newtype Typeable t => DEntry t = DE { unDE :: M.HashMap (PKey t) (Dep t) }
data DEntry' dep t where
  DE :: Fuzzable t => M.HashMap (PKey t) (dep t) -> DEntry' dep t

unDE :: DEntry' dep t -> M.HashMap (PKey t) (dep t)
unDE (DE de) = de

newtype SubEntry t = SE { unSE :: M.HashMap (PKey t) (PKey t) }

newtype SubEntry' t = SE' { unSE' :: M.HashMap (PKey t) (S.HashSet (PKey t)) }

newtype GroupEntry t = GE { unGE :: M.HashMap (PKey t) (PKey t) }

attrs2Deps :: NP Attribute t -> NP Dep t
attrs2Deps Nil       = Nil
attrs2Deps (a :* as) = DepAttr a :* attrs2Deps as

solveIndirects :: NodeDependence -> Dep p -> Dep p
solveIndirects dep (DepAttr (Get x)) = case lookupPKey x dep of
  Just d  -> solveIndirects dep d
  Nothing -> error "solveIndirects: should never be here"
solveIndirects _ d = d

unaliasVar :: Typeable p => NodeDependence -> PKey p -> Maybe (PKey p, Dep p)
unaliasVar dep x = case lookupPKey x dep of
  Just (DepAttr (Get y)) -> unaliasVar dep y
  Just other             -> Just (x, other)
  Nothing                -> Nothing

-- | Given 2 difference NodeDependence and 2 attribute lists, attempt to find a unification (i.e. Variable substitution scheme)
-- that makes all corresponding attributes in each list `effectively the same`.
getUnificationFromArgs :: forall p. (All Fuzzable p)
                       => NodeDependence -> NodeDependence -> NP Attribute p -> NP Attribute p -> Maybe VarSubstitution
getUnificationFromArgs d1 d2 Nil       Nil       = Just TM.empty
getUnificationFromArgs d1 d2 (a :* as) (b :* bs) = do
  u  <- unify (DepAttr a) (DepAttr b)
  us <- getUnificationFromArgs d1 d2 as bs
  unifyVarSubstitution u us
  where
    -- 2 variables are effectively the same, iff they point to some non-variable attribute that is the same.
    unify (DepAttr (Get x1)) (DepAttr (Get x2)) = do
      (_, dx1) <- unaliasVar d1 x1
      (_, dx2) <- unaliasVar d2 x2
      TM.adjust (SE . M.insert x2 x1 . unSE) <$> unify dx1 dx2
    -- Non-variable attributes are effectively the same, iff they are the same. (lol)
    unify (DepAttr a) (DepAttr b)
      | a == b    = Just TM.empty
      | otherwise = Nothing
    -- Api calls are the same, iff the function they calls are the same, and all arguments are pairwise-effectively the same.
    unify (DepCall f fa) (DepCall g ga) = case f `apiEqProofs` g of
      Nothing            -> Nothing
      Just (_, proof, _) -> getUnificationFromArgs d1 d2 (castWith (apply Refl proof) fa) ga
    -- Otherwise, not unifiable (e.g. x <-> some attr, not unifiable since x could be used in later context)
    unify _ _ = Nothing

-- | Unify 2 variable substitutions
-- Unification fails when a variable is assigned to 2 different variables in 2 subs.
unifyVarSubstitution :: VarSubstitution -> VarSubstitution -> Maybe VarSubstitution
unifyVarSubstitution vs1 vs2 = TM.hoistA unliftSE merge
  where
    -- Need to use helper SE' since @TM.unionWith@ only works for @f x -> f x -> f x@
    vs1'  = TM.hoist liftSE vs1
    vs2'  = TM.hoist liftSE vs2
    merge = TM.unionWith (\a b -> SE' $ M.unionWith S.union (unSE' a) (unSE' b)) vs1' vs2'

-- | Check if the a degraded dependencies is a subset of the other.
-- Relevant variable substitution must be applied first before calling this function.
-- Returns the String representation of the
isSubNodeDependence :: forall sig m. (Eff Empty sig m) => NodeDependence' DegradedDep -> NodeDependence' DegradedDep -> m String
isSubNodeDependence d1 d2 = D.toList <$> TM.fold collect (liftA2 (<>)) (return D.empty) (TM.hoist (Const . checkEachDEntry) d1)
  where
    collect :: forall t. Const (m (M.HashMap String String)) t -> m (D.DList Char)
    collect (Const m) = D.fromList . show <$> m

    -- | Check each DEntry in @d1@, whether we can find an subset in @d2@ that is isomorphic a la group.
    -- de1: DEntry in d1, de2: DEntry in d2
    checkEachDEntry :: forall t. DEntry' DegradedDep t -> m (M.HashMap String String)
    checkEachDEntry (DE de1) = M.map show . M.mapKeys show <$> unifyGroup (M.toList g1) M.empty
      where
        g1 = groupify (DE de1)
        g2 = groupify $ fromMaybe (DE M.empty) $ TM.lookup @t d2
        groupify (DE de) = M.mapWithKey (\k _ -> unaliasVar' de k) de

        -- | Given all keys and its relevant group ID in @g1@, find the possible group unification between @g1@ and @g2@
        unifyGroup []              ctx = return ctx
        unifyGroup ((k, dk1) : ks) ctx = do
          dk2 <- liftMaybe $ g2 M.!? k
          debug $ printf "Test.HAPI.AASTG.Analysis.Dependence.isSubNodeDependence.checkEachDEntry: Checking %s" (show (k, dk1, dk2))
          if dk1 /= dk2 then empty
                        else
            case ctx M.!? dk1 of
              Nothing                 -> unifyGroup ks (M.insert dk1 dk2 ctx)
              Just dk2' | dk2 == dk2' -> unifyGroup ks ctx
                        | otherwise   -> empty

        -- | Unalias variable, but in degraded map
        unaliasVar' de x = case de M.!? x of
          Just (DepAttr' (Get y)) -> unaliasVar' de y
          Just other              -> (x, other)
          Nothing                 -> error "Impossible"

-- | Utils

emptyDependence :: AASTG api c -> DependenceMap' dep
emptyDependence aastg = emptyDependence' [minNodeID aastg .. maxNodeID aastg]

emptyDependence' :: [NodeID] -> DependenceMap' dep
emptyDependence' ids = IM.fromAscList $ ids `zip` repeat TM.empty

lookupNode :: NodeID -> DependenceMap' dep -> NodeDependence' dep
lookupNode n = (IM.! n)

lookupPKey :: forall t dep. Typeable t => PKey t -> NodeDependence' dep -> Maybe (dep t)
lookupPKey p d = TM.lookup @t d >>= (M.!? p) . unDE

updatePKey :: forall t dep. Fuzzable t => PKey t -> dep t -> NodeDependence' dep -> NodeDependence' dep
updatePKey p a d = case TM.lookup @t d of
  Nothing     -> TM.insert (DE (M.singleton p a  )) d
  Just (DE m) -> TM.insert (DE (M.insert    p a m)) d

deletePKey :: forall t dep. Typeable t => PKey t -> NodeDependence' dep -> NodeDependence' dep
deletePKey p d = case TM.lookup @t d of
  Nothing     -> d
  Just (DE m) -> TM.insert (DE (M.delete p m)) d

updateDependence :: NodeID -> NodeDependence' dep -> DependenceMap' dep -> DependenceMap' dep
updateDependence = IM.insert

lookupPKeyInGroup :: forall t. Typeable t => PKey t -> GroupCtx -> Maybe (PKey t)
lookupPKeyInGroup t g = do
  (GE ge) <- TM.lookup @t g
  ge M.!? t

-- | Lift a SubEntry to SubEntry', where it is a key -> Set of key mapping
liftSE :: SubEntry t -> SubEntry' t
liftSE = SE' . M.map S.singleton . unSE

-- | Unlift a SubEntry' to SubEntry. If the SubEntry' contains a one-to-many mapping, then unlift fails.
unliftSE :: SubEntry' t -> Maybe (SubEntry t)
unliftSE (SE' se) = SE <$> M.foldrWithKey folder (Just M.empty) se
  where
    folder k s e
      | S.size s == 1 = M.insert k (head $ S.toList s) <$> e
      | otherwise     = Nothing

applyVarSubstitution :: VarSubstitution -> NodeDependence' dep -> NodeDependence' dep
applyVarSubstitution sub = TM.hoistWithKey $ \(de :: DEntry' dep t) -> case TM.lookup @t sub of
  Nothing -> de
  Just se -> applySE se de
  where
    applySE (SE se) (DE de) = DE $ M.union vs $ foldr M.delete de ks
      where
        ks = S.toList $ M.keysSet se `S.intersection` M.keysSet de
        vs = M.fromList [(se M.! k, de M.! k) | k <- ks]


getDependenceTable :: AASTG api c -> DependenceMap
getDependenceTable aastg = undefined

relevantDependence :: All Fuzzable p => NP PKey p -> NodeDependence -> NodeDependence
relevantDependence Nil       d = TM.empty
relevantDependence (k :* ks) d = updatePKey k (fromJust (lookupPKey k d)) (relevantDependence ks d)

pathDepCollector :: Has (State DependenceMap) sig m => TravHandler api c m
pathDepCollector = TravHandler $ \case
  OnNode n    -> return ()
  OnEdge edge -> do
    prev <- gets @DependenceMap $ lookupNode $ startNode edge
    let e = endNode edge
    new <- case edge of
      Update s e k a          -> return $ updatePKey k (DepAttr a) prev
      Forget s e x            -> return $ deletePKey x prev
      Assert s e x y          -> return prev
      APICall s e mx api args -> case mx of
        Nothing -> return prev
        Just x  -> return $ updatePKey x (DepCall api args) prev
    modify $ updateDependence @Dep e new

pathDeps :: forall api c p. (Path p) => p api c -> DependenceMap
pathDeps p = run
  . runState (\s _ -> return s) (emptyDependence' (pathNodesInSeq p))
  . runTrav @api @c pathDepCollector
  $ travPath p

pathDegradedDepCollector :: forall sig m api c. (Has (State DegradedDepMap) sig m, HasLabelled DegradedDep Fresh sig m) => TravHandler api c m
pathDegradedDepCollector = TravHandler $ \case
  OnNode n    -> return ()
  OnEdge edge -> do
    prev <- gets @DegradedDepMap $ lookupNode $ startNode edge
    let e = endNode edge
    new <- case edge of
      Update s e k a          -> return $ updatePKey k (DepAttr' a) prev
      Forget s e x            -> return $ deletePKey x prev
      Assert s e x y          -> return prev
      APICall s e mx api args -> case mx of
        Nothing -> return prev
        Just x  -> do
          i <- sendLabelled @DegradedDep Fresh
          return $ updatePKey x (DepCall' i) prev
    modify $ updateDependence @DegradedDep e new

pathDegradedDeps :: forall p api c. (Path p) => p api c -> DegradedDepMap
pathDegradedDeps p = run
  . runState (\s _ -> return s) (emptyDependence' (pathNodesInSeq p))
  . runFresh (\_ s -> return s) 0
  . runLabelled @DegradedDep
  . runTrav @api @c pathDegradedDepCollector
  $ travPath p


showDegDep :: NodeDependence' DegradedDep -> String
showDegDep = intercalate ", " . TM.degrade (\(DE de) -> show de)

-- Instances
instance (Show t) => Show (Dep t) where
  show (DepAttr at)     = "DepAttr(" <> show at  <> ")"
  show (DepCall api np) = "DepCall(" <> show api <> "(" <> intercalate "," (showAttributes np) <> ")"

instance (Eq t, Typeable t) => Eq (Dep t) where
  (DepAttr a)   == (DepAttr b)   = a == b
  (DepCall f a) == (DepCall g b) = case f `apiEqProofs` g of
    Nothing            -> False
    Just (_, proof, _) -> castWith (apply Refl proof) a `eqAttributes` b
  _ == _ = False

deriving instance Eq t => Eq (DegradedDep t)

instance Hashable t => Hashable (DegradedDep t) where
  -- DegradedDep will be used as a key, make it hashable.
  hashWithSalt salt (DepAttr' at) = salt
    `hashWithSalt` "a"
    `hashWithSalt` at
  hashWithSalt salt (DepCall' n) = salt
    `hashWithSalt` "c"
    `hashWithSalt` n

deriving instance Show t => Show (DegradedDep t)

