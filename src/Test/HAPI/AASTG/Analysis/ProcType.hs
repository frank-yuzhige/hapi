{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
module Test.HAPI.AASTG.Analysis.ProcType where

import Test.HAPI.Args (Attributes, Attribute (..), eqAttributes, attrs2Pat, DirectAttribute (..), eqAttributes', repEq)
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

import qualified Data.TypeRepMap as TM
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Type.Reflection (typeOf, typeRep)
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

newtype UnboundedProcTypeMap = UnboundedProcTypeMap { coerce2Bounded :: ProcTypeMap }

data Action where
  ActCall :: forall api p a c.
           ( ApiName api
           , Typeable p
           , Typeable c
           , All Fuzzable p
           , Fuzzable a)
        => PKey a
        -> api p a
        -> Attributes c p
        -> Action
  ActGen  :: forall a c.
           ( Fuzzable a
           , Typeable c)
        => PKey a
        -> Attribute c a
        -> Action
  ActAssert :: (Fuzzable Bool, Typeable c)
        => DirectAttribute c Bool
        -> Action
  ActContIf :: (Fuzzable Bool, Typeable c)
        => DirectAttribute c Bool
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

data Dep c t where
  DepAttr :: (Typeable c) =>                                             Attribute c t                       -> Dep c t
  DepCall :: (ApiName api, Typeable p, All Fuzzable p, Typeable c) => PKey t -> api p t -> Attributes c p -> Dep c t

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

(!*) :: UnboundedProcTypeMap -> NodeID -> ProcType
UnboundedProcTypeMap m !* n = m IM.! n

edge2Act :: (ApiName api) => Edge api c -> ProcType -> ProcType
edge2Act edge t = case edge of
  Update s e k a ->
    Act (ActGen k a) t
  ContIf s e p   ->
    Act (ActContIf p) t
  Assert s e p ->
    Act (ActAssert p) t
  APICall s e mx api args ->
    Act (ActCall mx api args) t
  Redirect n j ->
    t
-- | Infer Unbounded procedure types for all nodes in the given AASTG using iterative algorithm.
inferProcTypeUB :: forall sig m api c.
                       ( Alg sig m
                       , ApiName api )
                    => AASTG api c
                    -> m UnboundedProcTypeMap
inferProcTypeUB aastg
  = return $ UnboundedProcTypeMap $ foldr inferUnbounded IM.empty (allNodes aastg)
  where
    inferUnbounded i = IM.insert i (par ts)
      where
        ts = [ t' | edge <- edgesTo i aastg
                  , let t  = SVar (startNode edge)
                  , let t' = edge2Act edge t
                  ]


-- | Infer procedure types for all nodes in the given AASTG using iterative algorithm.
inferProcType :: forall sig m api c.
               ( Alg sig m
               , ApiName api )
            => AASTG api c
            -> m ProcTypeMap
inferProcType aastg = do
  -- debug $ printf "%s: Terminator Nodes %s" (show 'inferProcType) (show $ getTerminators aastg)
  unBounded2Bounded <$> inferProcTypeUB aastg

unBounded2Bounded :: UnboundedProcTypeMap -> ProcTypeMap
unBounded2Bounded = ground . coerce2Bounded
  where
    ground m = foldr groundOn m (IM.elems m >>= IS.toList . freeSVar)
    groundOn s m = IM.map (simplifyMu . subSVar s t') $ IM.insert s t' m
      where
        t = fromJust $ IM.lookup s m
        t' = if s `IS.member` freeSVar t
              then Mu s t
              else t

boundProcType :: UnboundedProcTypeMap -> ProcType -> ProcType
boundProcType uptm = go IS.empty
  where
    go bound = \case
      SVar x | IS.member x bound -> SVar x
             | otherwise         -> go bound (Mu x (uptm !* x))
      Act a t -> Act a (go bound t)
      Par ts  -> Par (map (go bound) ts)
      Mu x t  -> let t' = go (IS.insert x bound) t in
        if x `IS.member` freeSVar t' then Mu x t' else t'
      Zero    -> Zero


-- | Check if the given @sub@ type is a sub-type of the given @sup@ type
--   Return @Just@ the variable substitution that instantiates such sub-type relation, or @Nothing@ if @sub@ is not a sub-type of @sup@.
isSubType' :: Alg sig m => ProcType -> ProcType -> m (Maybe VarSubstitution)
isSubType' sub sup = runState (\s a -> return a) emptySubTypeCtx      -- Pitfall: first state then nondet. Other way round will stop propagation of state between (<|>)
  $ runNonDet (liftA2 (A.<|>)) (return . Just) (return Nothing)
  $ isSubType sub sup

-- | Check if the given @sub@ type is a sub-type of the given @sup@ type
--   Return the variable substitution that instantiates such sub-type relation.
isSubType :: forall sig m. (Eff (NonDet :+: State SubTypeCtx) sig m) => ProcType -> ProcType -> m VarSubstitution
isSubType = isSubTypeUB (UnboundedProcTypeMap IM.empty)

-- | Check if the given @sub@ type is a sub-type of the given @sup@ type
--   Return the variable substitution that instantiates such sub-type relation.
isSubTypeUB :: forall sig m.
             ( Eff (NonDet :+: State SubTypeCtx) sig m )
          => UnboundedProcTypeMap
          -> ProcType
          -> ProcType
          -> m VarSubstitution
isSubTypeUB (UnboundedProcTypeMap uptm) sub sup
  = do
  -- debug $ printf "%s: Checking ... \n>>  %s\n>>  %s" (show 'isSubTypeUB) (show sub) (show sup)
  sub ~<=~ sup
  where
    look x = fromMaybe Zero $ IM.lookup x uptm
    a ~<=~ b = do
      checked <- gets (HS.member (a, b) . view checkedPairs)
      if checked then return emptyVarSub else do
        modify $ over checkedPairs $ HS.insert (a, b)
        -- debug $ printf "%s: Checking ... \n>>  %s\n>>  %s" (show 'isSubTypeUB <> ":~<=~") (show a) (show b)
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
          (_, Par bs) -> do
            -- debug $ printf "%s: Checking RHS par" (show 'isSubTypeUB)
            cd <- gets (HS.member (a, b) . view checkedPairs)
            -- debug $ printf "%s: HS Member: %s" (show 'isSubTypeUB) (show cd)
            checkAny bs
            where
              checkAny []         = empty
              checkAny (b' : bs') = a ~<=~ b' <|> checkAny bs' --- ???
          (Act a'@(ActGen xa ga) ta, Act b'@(ActGen xb gb) tb) -> do
            -- debug $ printf "%s: here" (show 'isSubTypeUB)
            proof <- liftMaybe $ testEquality (typeOf ga) (typeOf gb)
            let s0 = singletonVarSub xb (castWith (apply Refl $ inner proof) xa)
            s1 <- getVarSubFromArgs look look a b (castWith proof ga :* Nil) (gb :* Nil)
            -- debug $ printf "%s: varsub ok" (show 'isSubTypeUB)
            s2 <- liftMaybe $ s0 `unifyVarSubstitution` s1
            s3 <- ta ~<=~ tb
            liftMaybe $ s2 `unifyVarSubstitution` s3
          (Act a'@(ActCall xa fa as) ta, Act b'@(ActCall xb fb bs) tb) -> do
            (_, !pp, pa) <- liftMaybe $ apiEqProofs fa fb
            sproof <- liftMaybe $ testEquality (typeOf as) (typeOf bs)
            let as' = castWith sproof as
                xa' = castWith (apply Refl pa) xa
                s0  = singletonVarSub xb xa'
            -- debug $ printf "%s: API call is eq" (show 'isSubTypeUB)
            s1 <- getVarSubFromArgs look look a b as' bs
            -- debug $ printf "%s: varsub ok" (show 'isSubTypeUB)
            s2 <- liftMaybe $ s0 `unifyVarSubstitution` s1
            -- debug $ printf "%s: unify ok" (show 'isSubTypeUB)
            s3 <- ta ~<=~ tb
            liftMaybe $ s2 `unifyVarSubstitution` s3
          (Act a'@(ActAssert da) ta, Act b'@(ActAssert db) tb) -> do
            proof <- liftMaybe $ testEquality (typeOf da) (typeOf db)
            s1 <- getVarSubFromArgs look look a b (Direct (castWith proof da) :* Nil) (Direct db :* Nil)
            s2 <- ta ~<=~ tb
            liftMaybe $ unifyVarSubstitution s1 s2
          (Act a'@(ActContIf da) ta, Act b'@(ActContIf db) tb) -> do
            proof <- liftMaybe $ testEquality (typeOf da) (typeOf db)
            s1 <- getVarSubFromArgs look look a b (Direct (castWith proof da) :* Nil) (Direct db :* Nil)
            s2 <- ta ~<=~ tb
            liftMaybe $ unifyVarSubstitution s1 s2
            -- if a == b then ta ~<=~ tb else empty
          -- (Act a'@(ActAssert (Get xa)) ta, Act b'@(ActAssert (Get xb)) tb) -> do
          --   let s0 = singletonVarSub xb xa
          --   s1 <- ta ~<=~ tb
          --   liftMaybe $ s0 `unifyVarSubstitution` s1
          _ -> empty

-- | Given 2 different procedure types and 2 attribute lists, attempt to find a unification (i.e. PKey substitution scheme)
-- that makes all corresponding attributes in each list `effectively the same`.
-- TODO use de brujin implicit (https://cs.stackexchange.com/questions/76616/algorithm-for-deciding-alpha-equivalence-of-terms-in-languages-with-bindings)
getVarSubFromArgs :: forall p c sig m.
                   ( All Fuzzable p
                   , Eff NonDet sig m
                   , Typeable c)
                => (SVar -> ProcType)
                -> (SVar -> ProcType)
                -> ProcType
                -> ProcType
                -> Attributes c p
                -> Attributes c p
                -> m VarSubstitution
getVarSubFromArgs look1 look2 d1 d2 Nil       Nil       = return emptyVarSub
getVarSubFromArgs look1 look2 d1 d2 (a :* as) (b :* bs) = do
  -- debug $ printf "%s: subbing %s" (show 'getVarSubFromArgs) (show (a, b))
  u  <- unify (DepAttr a) (DepAttr b)
  us <- getVarSubFromArgs look1 look2 d1 d2 as bs
  liftMaybe $ unifyVarSubstitution u us
  where
    unify (DepAttr (Direct d1)) (DepAttr (Direct d2)) = unifyDirect d1 d2
      where
        go :: Fuzzable x => DirectAttribute c x -> DirectAttribute c x -> DirectAttribute c x -> DirectAttribute c x -> m VarSubstitution
        go a a1 b b1 = do
          x <- a `unifyDirect` a1
          y <- b `unifyDirect` b1
          liftMaybe (unifyVarSubstitution x y)
        unifyDirect :: Fuzzable x => DirectAttribute c x -> DirectAttribute c x -> m VarSubstitution
        (Get a)          `unifyDirect` (Get a')          = return (singletonVarSub a' a)
        (DNot a)         `unifyDirect` (DNot a')         = a `unifyDirect` a'
        (DAnd a1 a2)     `unifyDirect` (DAnd a1' a2')    = go a1 a1' a2 a2'
        (DOr  a1 a2)     `unifyDirect` (DOr  a1' a2')    = go a1 a1' a2 a2'
        (DPlus a1 a2)    `unifyDirect` (DPlus a1' a2')   = go a1 a1' a2 a2'
        (DMinus a1 a2)   `unifyDirect` (DMinus a1' a2')  = go a1 a1' a2 a2'
        (DMul a1 a2)     `unifyDirect` (DMul a1' a2')    = go a1 a1' a2 a2'
        (DDiv a1 a2)     `unifyDirect` (DDiv a1' a2')    = go a1 a1' a2 a2'
        (DNeg da)        `unifyDirect` (DNeg da')        = da `unifyDirect` da'
        (DCmp c a1 a2)   `unifyDirect` (DCmp c' a1' a2') = case testEquality (typeOf a1) (typeOf a1') of
          Just proof | c == c' -> go (castWith proof a1) a1' (castWith proof a2) a2'
          _                    -> empty
        (DEq  b a1 a2)   `unifyDirect` (DEq  b' a1' a2') = case testEquality (typeOf a1) (typeOf a1') of
          Just proof | b == b' -> go (castWith proof a1) a1' (castWith proof a2) a2'
          _                    -> empty
        (DCastInt a)     `unifyDirect` (DCastInt a')     = case testEquality (typeOf a) (typeOf a') of
          Just proof -> unifyDirect (castWith proof a) a'
          _          -> empty
        otherA `unifyDirect` otherB
          | otherA == otherB = return TM.empty
          | otherwise        = empty
    unify (DepAttr a) (DepAttr b)
      | a == b    = return TM.empty
      | otherwise = empty
    -- -- 2 variables are effectively the same, iff they point to some non-variable attribute that is the same.
    -- -- unify (DepAttr (Direct (Get x1))) (DepAttr (Direct (Get x2))) = do
    --   -- debug $ printf "%s: var start %s" (show 'getVarSubFromArgs <> ".unify") (show (x1, x2))
    --   -- dx1 <- lookupPKInType look1 x1 d1
    --   -- debug $ printf "%s: var %s;" (show 'getVarSubFromArgs <> ".unify") (show (x1, dx1))
    --   -- dx2 <- lookupPKInType look2 x2 d2
    --   -- debug $ printf "%s: var %s;" (show 'getVarSubFromArgs <> ".unify") (show (x2, dx2))
    --   -- TM.adjust (SE . HM.insert x2 x1 . unSE) <$> unify dx1 dx2
    --   -- return (singletonVarSub x2 x1)
    -- -- Non-variable attributes are effectively the same, iff they are the same. (lol)
    -- unify (DepAttr a) (DepAttr b)
    --   | a == b    = return TM.empty
    --   | otherwise = empty
    -- Api calls are the same, iff the function they calls are the same, and all arguments are pairwise-effectively the same.
    unify (DepCall x1 f fa) (DepCall x2 g ga) = do
      (_, proof, _) <- liftMaybe $ f `apiEqProofs` g
      s' <- getVarSubFromArgs look1 look2 d1 d2 (castWith (apply Refl proof) fa) ga
      liftMaybe $ singletonVarSub x2 x1 `unifyVarSubstitution` s'
    -- Otherwise, not unifiable (e.g. x <-> some attr, not unifiable since x could be used in later context)
    unify _ _ = empty

lookupPKInType :: forall t c sig m. (Fuzzable t, Eff NonDet sig m, Typeable c)
               => (SVar -> ProcType)
               -> PKey t
               -> ProcType
               -> m [Dep c t]
lookupPKInType look k t = do
  d <- go IS.empty t
  -- debug $ printf "%s: k = %s; v = %s" (show 'lookupPKInType) (show k) (show d)
  return d
  where
    go history = \case
      SVar x | IS.member x history -> empty
             | otherwise           -> go (IS.insert x history) (look x)
      Act a t -> case a of
        ActGen  x at -> do
          case inner <$> testEquality (typeOf x) (typeOf k) of
            Just proof | castWith (apply Refl proof) x == k
              -> let d = DepAttr at in case testEquality (typeOf d) (typeRep @(Dep c t)) of
                Just cproof -> return [castWith cproof d]
                Nothing     -> go history t
            _ -> go history t
        ActCall x api as -> do
          case inner <$> testEquality (typeOf x) (typeOf k) of
            Just proof | castWith (apply Refl proof) x == k
              -> let d = DepCall x api as in case testEquality (typeOf d) (typeRep @(Dep c t)) of
                Just cproof -> return [castWith cproof d]
                Nothing     -> go history t
            _ -> go history t
        _ -> do
          go history t
      Par ts -> foldr (liftA2 (<>) . go history) empty ts
      Mu s t -> go history t
      Zero   -> empty

instance Eq Action where
  ActCall m f as == ActCall n g bs = case apiEqProofs f g of
    Nothing        -> False
    Just (_, p, a) -> castWith (apply Refl a) m == n
                   && castWith (apply Refl p) as `eqAttributes'` bs
  ActGen x a == ActGen y b = case testEquality (typeOf a) (typeOf b) of
    Nothing    -> False
    Just proof -> castWith (apply Refl $ inner proof) x == y
               && castWith proof a == b
  ActAssert p   == ActAssert q = case testEquality (typeOf p) (typeOf q) of
    Nothing    -> False
    Just proof -> castWith proof p == q
  ActContIf p   == ActContIf q = case testEquality (typeOf p) (typeOf q) of
    Nothing    -> False
    Just proof -> castWith proof p == q
  _ == _ = False

instance Show Action where
  show (ActCall x api args)
    = printf "%s=%s" (getPKeyID x) (showApiFromPat api (attrs2Pat args))
  show (ActGen x a)
    = printf "%s=%s" (getPKeyID x) (show a)
  show (ActAssert p)
    = printf "?{%s}" (show p)
  show (ActContIf p)
    = printf "?%s" (show p)

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
  hashWithSalt salt (ActAssert p) = salt
    `hashWithSalt` "Assert"
    `hashWithSalt` p
  hashWithSalt salt (ActContIf p) = salt
    `hashWithSalt` "ContIf"
    `hashWithSalt` p

deriving instance Generic ProcType
instance Hashable ProcType

deriving instance Show SubTypeCtx

deriving instance Show UnboundedProcTypeMap
deriving instance Eq UnboundedProcTypeMap

instance (Show t) => Show (Dep c t) where
  show (DepAttr at)       = "DepAttr(" <> show at  <> ")"
  show (DepCall x api np) = "DepCall(" <> show x <> "=" <> showApiFromPat api (attrs2Pat np) <> ")"

instance (Eq t, Typeable t) => Eq (Dep c t) where
  (DepAttr a)     == (DepAttr b)     = a == b
  (DepCall x f a) == (DepCall y g b) = case f `apiEqProofs` g of
    Nothing            -> False
    Just (_, proof, _) -> castWith (apply Refl proof) a `eqAttributes` b
                       && x == y
  _ == _ = False
