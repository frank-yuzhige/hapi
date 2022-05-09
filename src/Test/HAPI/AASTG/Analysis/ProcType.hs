{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Test.HAPI.AASTG.Analysis.ProcType where

import Test.HAPI.Args (Attributes, Attribute (..), eqAttributes, attrs2Pat)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.PState (PKey(..))
import Test.HAPI.Api (ApiName (..), apiEqProofs, isExternalPure)
import Data.SOP (All, NP (..))
import Data.Type.Equality (castWith, apply,type  (:~:) (Refl), testEquality, inner)
import Data.Data (Typeable)
import Test.HAPI.Effect.Eff (Eff, debug, Alg, runEnv, (:+:))
import Control.Effect.Empty (Empty, empty)
import Control.Carrier.State.Church (runState)
import Data.Set (Set)
import Data.Hashable (Hashable(..))
import qualified Data.HashSet as HS
import Data.HashSet (HashSet)
import Control.Lens (makeLenses, view, over)
import Control.Effect.State (gets, modify, get, State)
import GHC.Generics (Generic)
import Test.HAPI.Util.Empty (liftMaybe)
import Control.Carrier.Cull.Church (NonDet)
import Control.Effect.Choose ((<|>))

import Test.HAPI.AASTG.Analysis.Dependence (Dep(..))
import qualified Data.TypeRepMap as TM
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Type.Reflection (typeOf)
import qualified Data.HashMap.Strict as HM
import Text.Printf (printf)
import Data.IntMap (IntMap)
import Data.Maybe (fromJust, fromMaybe)
import Data.IntSet (IntSet)
import Test.HAPI.AASTG.Core (NodeID, Edge (..), allNodes, AASTG (..), startNode, edgesTo, getTerminators)
import Control.Monad (forM_, forM, join)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR))
import Data.List (intercalate)
import Test.HAPI.AASTG.Analysis.Rename (VarSubstitution, emptyVarSub, SubEntry (..), singletonVarSub, unifyVarSubstitution)
import Control.Carrier.NonDet.Church (runNonDet)
import Control.Applicative (liftA2)
import qualified Control.Applicative as A

type SVar = NodeID

type ProcTypeMap = IntMap ProcType

newtype UngroundProcTypeMap = UngroundProcTypeMap { coerce2Grounded :: ProcTypeMap }

data Action where
  ActCall :: forall api p a.
           ( ApiName api
           , Typeable p
           , All Fuzzable p
           , Fuzzable a)
        => PKey a
        -> api p a
        -> Attributes p
        -> Action
  ActGen  :: forall a.
           ( Fuzzable a )
        => PKey a
        -> Attribute a
        -> Action


data SubTypeCtx = SubTypeCtx {
  _checkedPairs :: HashSet (ProcType, ProcType),
  _nmb          :: String
}

data ProcType
  = SVar SVar
  | Act  Action ProcType
  | Par  [ProcType]
  | Mu   SVar ProcType
  | Zero

$(makeLenses ''SubTypeCtx)

-- Smart Par that auto evals to Zero if list is empty, or just the element if the list only contains that element.
par :: [ProcType] -> ProcType
par []  = Zero
par [t] = t
par xs  = Par xs

emptySubTypeCtx :: SubTypeCtx
emptySubTypeCtx = SubTypeCtx HS.empty ""

-- | Unwind Recursion construct (μ) once.
--   For any other constructs, remain what it was.
unroll :: ProcType -> ProcType
unroll t@(Mu x t') = go t'
  where
    go (SVar y)
      | x == y    = t
      | otherwise = SVar y
    go (Act a t') = Act a (go t')
    go (Par ts)   = Par (map go ts)
    go (Mu y t')
      | x == y    = Mu y t'
      | otherwise = Mu y (go t')
    go Zero       = Zero
unroll t = t

-- | Get a set of free SVars
freeSVar :: ProcType -> IntSet
freeSVar (SVar v)  = IS.singleton v
freeSVar (Act a t) = freeSVar t
freeSVar (Par ts)  = IS.unions (map freeSVar ts)
freeSVar (Mu n t)  = IS.delete n $ freeSVar t
freeSVar Zero      = IS.empty

-- | Given SVar V, type S and type T, Substitute all free occurrences of V in T with S
subSVar :: SVar -> ProcType -> ProcType -> ProcType
subSVar v s = \case
  SVar x | x == v    -> s
         | otherwise -> SVar x
  Act a t -> Act a (subSVar v s t)
  Par ts  -> Par (map (subSVar v s) ts)
  Mu x t | x == v    -> Mu x t
         | otherwise -> Mu x (subSVar v s t)
  Zero    -> Zero

isValidType :: ProcType -> Bool
isValidType x = IS.null $ freeSVar x

-- | Simplify the Recursive construct, by removing all unnecessary μ-constructs when quantified no SVar.
simplifyMu :: ProcType -> ProcType
simplifyMu (Mu x t)
  | x `IS.member` freeSVar t = Mu x (simplifyMu t)
  | otherwise                = simplifyMu t
simplifyMu (Act a t) = Act a (simplifyMu t)
simplifyMu (Par ts)  = Par (map simplifyMu ts)
simplifyMu (SVar x)  = SVar x
simplifyMu Zero      = Zero

(!*) :: UngroundProcTypeMap -> NodeID -> ProcType
UngroundProcTypeMap m !* n = m IM.! n

-- | Infer unground procedure types for all nodes in the given AASTG using iterative algorithm.
inferProcTypeUG :: forall sig m api c.
                       ( Alg sig m
                       , ApiName api )
                    => AASTG api c
                    -> m UngroundProcTypeMap
inferProcTypeUG aastg
  = return $ UngroundProcTypeMap $ foldr inferUnground IM.empty (allNodes aastg)
  where
    inferUnground i = IM.insert i (par ts)
      where
        ts = [ tau' | edge <- edgesTo i aastg
                    , let tau  = SVar (startNode edge)
                    , let tau' = case edge of
                            Update s e k a ->
                              Act (ActGen k a) tau
                            Forget s e x   ->
                              fatalError 'inferProcType FATAL_ERROR "Unsupported construct 'forget'"
                            Assert n j pk pk' ->
                              fatalError 'inferProcType FATAL_ERROR "Unsupported construct 'assert'"
                            APICall s e mx api args ->
                              Act (ActCall mx api args) tau
                            Redirect n j ->
                              tau
                    ]


-- | Infer procedure types for all nodes in the given AASTG using iterative algorithm.
inferProcType :: forall sig m api c.
               ( Alg sig m
               , ApiName api )
            => AASTG api c
            -> m ProcTypeMap
inferProcType aastg = do
  -- debug $ printf "%s: Terminator Nodes %s" (show 'inferProcType) (show $ getTerminators aastg)
  ground . coerce2Grounded <$> inferProcTypeUG aastg
  where
    ground m = foldr groundOn m (IM.elems m >>= IS.toList . freeSVar)
    groundOn s m = IM.map (simplifyMu . subSVar s t') $ IM.insert s t' m
      where
        t = fromJust $ IM.lookup s m
        t' = if s `IS.member` freeSVar t
              then Mu s t
              else t

-- | Check if the given procedure type is well-formed. A well-formed procedure type should satisfy the following statements:
--     1. It does not contain any `free` SVar (state variable).
--     2.
checkValidType :: forall sig m api c.
                ( Alg sig m
                , ApiName api )
             => AASTG api c
             -> m ProcTypeMap
checkValidType = undefined

-- | Check if the given @sub@ type is a sub-type of the given @sup@ type
--   Return @Just@ the variable substitution that instantiates such sub-type relation, or @Nothing@ if @sub@ is not a sub-type of @sup@.
isSubType' :: ProcType -> ProcType -> Maybe VarSubstitution
isSubType' sub sup = runEnv
  $ runState (\s a -> return a) emptySubTypeCtx      -- Pitfall: first state then nondet. Other way round will stop propagation of state between (<|>)
  $ runNonDet (liftA2 (A.<|>)) (return . Just) (return Nothing)
  $ isSubType sub sup

-- | Check if the given @sub@ type is a sub-type of the given @sup@ type
--   Return the variable substitution that instantiates such sub-type relation.
isSubType :: forall sig m. (Eff (NonDet :+: State SubTypeCtx) sig m) => ProcType -> ProcType -> m VarSubstitution
isSubType = isSubTypeUG (UngroundProcTypeMap IM.empty)
  -- debug $ printf "%s: Checking ... \n>>  %s\n>>  %s" (show 'isSubType) (show sub) (show sup)
  -- sub ~<=~ sup
  -- where
  --   a ~<=~ b = do
  --     checked <- gets (HS.member (a, b) . view checkedPairs)
  --     if checked then return emptyVarSub else do
  --       modify $ over checkedPairs $ HS.insert (a, b)
  --       case (a, b) of
  --         (Zero, Zero) ->
  --           return emptyVarSub
  --         (Mu {}, _) ->
  --           unroll a ~<=~ b
  --         (_, Mu {}) ->
  --           a ~<=~ unroll b
  --         (Par as, _) -> do
  --           vs <- mapM (~<=~ b) as
  --           liftMaybe $ foldr (\v a -> a >>= unifyVarSubstitution v) (Just emptyVarSub) vs
  --         (_, Par bs) -> checkAny bs
  --           where
  --             checkAny []         = empty
  --             checkAny (b' : bs') = a ~<=~ b' <|> checkAny bs'
  --         -- Ignoring variable from attributes and external-pure functions (e.g. Anything)
  --         (Act (ActGen _ _) ta, _)
  --           -> ta ~<=~ b
  --         (_, Act (ActGen _ _) tb)
  --           -> a ~<=~ tb
  --         (Act (ActCall _ a _) ta, _) | isExternalPure a
  --           -> ta ~<=~ b
  --         (_, Act (ActCall _ b _) tb) | isExternalPure b
  --           -> a ~<=~ tb
  --         (Act a'@(ActCall xa a as) ta, Act b'@(ActCall xb b bs) tb) -> do
  --           (papi, pp, pa) <- liftMaybe $ apiEqProofs a b
  --           let as' = castWith (apply Refl pp) as
  --           let s0  = singletonVarSub xb (castWith (apply Refl pa) xa)
  --           s1 <- getVarSubFromArgs sub sup as' bs
  --           s1' <- liftMaybe $ s0 `unifyVarSubstitution` s1
  --           s2 <- ta ~<=~ tb
  --           liftMaybe $ s1' `unifyVarSubstitution` s2
  --         _ -> empty

-- | Check if the given @sub@ type is a sub-type of the given @sup@ type
--   Return the variable substitution that instantiates such sub-type relation.
isSubTypeUG :: forall sig m.
             ( Eff (NonDet :+: State SubTypeCtx) sig m )
          => UngroundProcTypeMap
          -> ProcType
          -> ProcType
          -> m VarSubstitution
isSubTypeUG (UngroundProcTypeMap uptm) sub sup
  = do
  -- debug $ printf "%s: Checking ... \n>>  %s\n>>  %s" (show 'isSubTypeUG) (show sub) (show sup)
  sub ~<=~ sup
  where
    look x = fromMaybe Zero $ IM.lookup x uptm
    a ~<=~ b = do
      -- debug $ printf "%s: Checking ... \n>>  %s\n>>  %s" (show 'isSubTypeUG <> ":~<=~") (show a) (show b)
      checked <- gets (HS.member (a, b) . view checkedPairs)
      if checked then return emptyVarSub else do
        modify $ over checkedPairs $ HS.insert (a, b)
        case (a, b) of
          (Zero, Zero) ->
            return emptyVarSub
          (SVar x, _) ->
            look x ~<=~ b
          (_, SVar y) ->
            a ~<=~ look y
          (Mu {}, _) ->
            unroll a ~<=~ b
          (_, Mu {}) ->
            a ~<=~ unroll b
          (Par as, _) -> do
            vs <- mapM (~<=~ b) as
            liftMaybe $ foldr (\v a -> a >>= unifyVarSubstitution v) (Just emptyVarSub) vs
          (_, Par bs) -> checkAny bs
            where
              checkAny []         = empty
              checkAny (b' : bs') = a ~<=~ b' <|> checkAny bs'
          -- Ignoring variable from attributes and external-pure functions (e.g. Anything)
          (Act (ActGen _ _) ta, _)
            -> ta ~<=~ b
          (_, Act (ActGen _ _) tb)
            -> a ~<=~ tb
          (Act (ActCall _ a _) ta, _) | isExternalPure a
            -> ta ~<=~ b
          (_, Act (ActCall _ b _) tb) | isExternalPure b
            -> a ~<=~ tb
          (Act a'@(ActCall xa a as) ta, Act b'@(ActCall xb b bs) tb) -> do
            (_, pp, pa) <- liftMaybe $ apiEqProofs a b
            let as' = castWith (apply Refl pp) as
                xa' = castWith (apply Refl pa) xa
                s0  = singletonVarSub xb xa'
            s1 <- getVarSubFromArgs look sub sup as' bs
            s1' <- liftMaybe $ s0 `unifyVarSubstitution` s1
            s2 <- ta ~<=~ tb
            liftMaybe $ s1' `unifyVarSubstitution` s2
          _ -> empty

-- | Given 2 different procedure types and 2 attribute lists, attempt to find a unification (i.e. SVar substitution scheme)
-- that makes all corresponding attributes in each list `effectively the same`.
getVarSubFromArgs :: forall p sig m.
                   ( All Fuzzable p
                   , Eff NonDet sig m)
                => (SVar -> ProcType)
                -> ProcType
                -> ProcType
                -> Attributes p
                -> Attributes p
                -> m VarSubstitution
getVarSubFromArgs look d1 d2 Nil       Nil       = return emptyVarSub
getVarSubFromArgs look d1 d2 (a :* as) (b :* bs) = do
  u  <- unify (DepAttr a) (DepAttr b)
  us <- getVarSubFromArgs look d1 d2 as bs
  liftMaybe $ unifyVarSubstitution u us
  where
    -- 2 variables are effectively the same, iff they point to some non-variable attribute that is the same.
    unify (DepAttr (Get x1)) (DepAttr (Get x2)) = do
      (_, dx1) <- unaliasVar look d1 x1
      (_, dx2) <- unaliasVar look d2 x2
      TM.adjust (SE . HM.insert x2 x1 . unSE) <$> unify dx1 dx2
    -- Non-variable attributes are effectively the same, iff they are the same. (lol)
    unify (DepAttr a) (DepAttr b)
      | a == b    = return TM.empty
      | otherwise = empty
    -- Api calls are the same, iff the function they calls are the same, and all arguments are pairwise-effectively the same.
    -- TODO: Same api call, different location?
    unify (DepCall f fa) (DepCall g ga) = do
      (_, proof, _) <- liftMaybe $ f `apiEqProofs` g
      getVarSubFromArgs look d1 d2 (castWith (apply Refl proof) fa) ga
    -- Otherwise, not unifiable (e.g. x <-> some attr, not unifiable since x could be used in later context)
    unify _ _ = empty

unaliasVar :: (Typeable p, Eff NonDet sig m) => (SVar -> ProcType) -> ProcType -> PKey p -> m (PKey p, Dep p)
unaliasVar look t x = do
  n <- lookupPKInType look x t
  case n of
    (DepAttr (Get y)) -> unaliasVar look t y
    other             -> return (x, other)

lookupPKInType :: (Typeable t, Eff NonDet sig m) => (SVar -> ProcType) -> PKey t -> ProcType -> m (Dep t)
lookupPKInType look k = go IS.empty
  where
    go history = \case
      SVar x | IS.member x history -> empty
             | otherwise           -> go (IS.insert x history) (look x)
      Act a t  -> case a of
        ActGen  x at -> do
          proof <- liftMaybe $ inner <$> testEquality (typeOf x) (typeOf k)
          if castWith (apply Refl proof) x == k
            then return $ castWith (apply Refl proof) $ DepAttr at
            else go history t
        ActCall x api as -> do
          proof <- liftMaybe $ inner <$> testEquality (typeOf x) (typeOf k)
          if castWith (apply Refl proof) x == k
            then return $ castWith (apply Refl proof) $ DepCall api as
            else go history t
      Par ts -> foldr ((<|>) . go history) empty ts
      Mu s t -> go history t
      Zero   -> empty

instance Eq Action where
  ActCall m f as == ActCall n g bs = case apiEqProofs f g of
    Nothing        -> False
    Just (_, p, a) -> castWith (apply Refl a) m == n
                   && castWith (apply Refl p) as `eqAttributes` bs
  ActGen x a == ActGen y b = case testEquality (typeOf x) (typeOf y) of
    Nothing    -> False
    Just proof -> castWith proof x == y
               && castWith (apply Refl $ inner proof) a == b
  _ == _ = False

instance Show Action where
  show (ActCall x api args)
    = printf "%s=%s" (getPKeyID x) (showApiFromPat api (attrs2Pat args))
  show (ActGen x a)
    = printf "%s=%s" (getPKeyID x) (show a)

deriving instance Eq ProcType

instance Show ProcType where
  show (SVar v)  = printf "X%d" v
  show (Act a t) = printf "%s.%s" (show a) (show t)
  show (Par ts)  = "(" <> intercalate " | " (map show ts) <> ")"
  show (Mu n t)  = printf "μX%d.%s" n (show t)
  show Zero      = "0"


instance Hashable Action where
  hashWithSalt salt (ActCall mx api args) = salt
    `hashWithSalt` "Call"
    `hashWithSalt` mx
    `hashWithSalt` apiName api
    `hashWithSalt` args
  hashWithSalt salt (ActGen x a) = salt
    `hashWithSalt` "Gen"
    `hashWithSalt` x
    `hashWithSalt` a

deriving instance Generic ProcType
instance Hashable ProcType

deriving instance Show SubTypeCtx

deriving instance Show UngroundProcTypeMap
deriving instance Eq   UngroundProcTypeMap
