{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}

{-
Exogenous Value Generation Effect
-}

module Test.HAPI.Effect.EVS where
import Control.Algebra (Algebra (alg), type (:+:) (L, R), Has, send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Test.HAPI.Effect.Gen (GenAC(runGenAC), GenA (LiftGenA), liftGenA)
import Test.QuickCheck (Arbitrary(arbitrary), chooseInt, chooseEnum)
import Data.Kind (Constraint, Type)
import Data.Functor (($>))
import Control.Carrier.State.Church (StateC, get)
import Control.Effect.State ( State, gets )
import Control.Effect.Sum (Member, Members)
import Test.QuickCheck.Gen (Gen)
import Test.QuickCheck.GenT (MonadGen (liftGen))
import Test.HAPI.PState (PKey, PState, PStateSupports (lookUp))
import Test.HAPI.Common (Fuzzable)
import Data.Maybe (fromJust)
import Data.HList (HList (HNil), HMap,type  (:~:) (Refl))
import Data.SOP ( Proxy(Proxy), NP(..), All, hcmap, I (..), type (:.:) (Comp) )
import Test.HAPI.Args (Args, pattern (::*), Attribute (..), validate, DirectAttribute (..), ExogenousAttribute (..), Attributes, evalDirect, DirAttributes, simplifyDirect)
import Data.SOP.Dict (mapAll)
import Data.Serialize (Serialize)
import Test.HAPI.Effect.Orchestration (Orchestration, nextInstruction, OrchestrationError)
import Test.HAPI.Effect.Orchestration.Labels (EVSSupply)
import Data.Type.Equality (castWith, TestEquality (testEquality), apply)
import Type.Reflection ( TypeRep, typeOf, Typeable, typeRep )
import Test.HAPI.Constraint (type (:>>>:), witnessC, CMembers)
import Data.Constraint ((\\), mapDict, Dict (..))
import Control.Effect.Error (Error, liftEither, throwError)
import Control.Carrier.Error.Either (runError)
import Data.Either.Combinators (mapLeft)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR))
import Test.HAPI.Serialize (HSerialize)
import qualified Test.HAPI.Serialize as HS
import qualified Data.Serialize as S
import Control.Applicative (liftA2)


-- Exogenous Value Supplier
data EVS (c :: Type -> Constraint) (m :: Type -> Type) a where
  EExogenous :: (Fuzzable a, c a) => ExogenousAttribute c a -> EVS c m (DirectAttribute c a)

data EVSError = EVSError { causedAttribute :: String, errorMessage :: String }
  deriving Show

mkEVS :: forall c a m. Typeable c => Attribute c a -> EVS c m (DirectAttribute c a)
mkEVS (Exogenous e) = EExogenous e


-- | Convert attribute to EVS
attributes2EVSs :: forall c p m. Typeable c => Attributes c p -> NP (EVS c m :.: DirectAttribute c) p
attributes2EVSs Nil = Nil
attributes2EVSs (a :* as) = Comp (mkEVS a) :* attributes2EVSs as

-- | Generate values in HList
evs2m :: (Has (EVS c) sig m) => NP (EVS c m :.: f) p -> m (NP f p)
evs2m Nil = return Nil
evs2m (Comp evs :* q) = do
  a <- send evs
  s <- evs2m q
  return (a :* s)

resolveAttrViaEVS :: forall c a sig m. (Has (EVS c) sig m) => Attribute c a -> m (DirectAttribute c a)
resolveAttrViaEVS = \case
  Direct    d -> return d
  Exogenous e -> send $ EExogenous @_ @c e

resolveAttrsViaEVS :: forall c p sig m. (Has (EVS c) sig m) => Attributes c p -> m (DirAttributes c p)
resolveAttrsViaEVS Nil       = return Nil
resolveAttrsViaEVS (a :* as) = liftA2 (:*) (resolveAttrViaEVS a) (resolveAttrsViaEVS as)

newtype EVSFuzzArbitraryAC (c :: Type -> Constraint) m a = EVSFuzzArbitraryAC { runEVSFuzzArbitraryAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

instance (Algebra sig m, Members (State PState :+: GenA) sig, CMembers Arbitrary c) => Algebra (EVS c :+: sig) (EVSFuzzArbitraryAC c m) where
  alg hdl sig ctx = EVSFuzzArbitraryAC $ case sig of
    L evs   -> resolveEVS evs
    R other -> alg (runEVSFuzzArbitraryAC . hdl) other ctx
    where
      resolveEVS evs = case evs of
        EExogenous (Anything :: ExogenousAttribute c a) -> do
          v <- liftGenA (arbitrary @a \\ witnessC @Arbitrary @c @a)
          return (ctx $> Value v)
        EExogenous (IntRange l r) -> do
          v <- Value <$> liftGenA (chooseInt (l, r))
          return (ctx $> v)
        EExogenous (Range    l r) -> do
          v <- Value <$> liftGenA (chooseEnum (l, r))
          return (ctx $> v)
        -- Exogenous AnyOf xs     -> do
          -- a <- oneof' (return <$> xs)
          -- resolveEVS (EVS a)

newtype EVSFromStdinAC (c :: Type -> Constraint) m a = EVSFromStdinAC { runEVSFromStdinAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance ( Algebra sig m
         , Has (Error EVSError)          sig m
         , Has (State PState)            sig m
         , MonadIO m
         , CMembers Read c)
      => Algebra (EVS c :+: sig) (EVSFromStdinAC c m) where
  alg hdl sig ctx = EVSFromStdinAC $ case sig of
    L (EExogenous (a :: ExogenousAttribute c a) ) -> do
      liftIO $ print a
      input <- liftIO (putStrLn "Please provide input: " >> readAndValidate a) \\ witnessC @Read @c @a
      return (ctx $> Value input)
    R other -> alg (runEVSFromStdinAC . hdl) other ctx
    where
      readAndValidate attr = do
        a <- readLn
        if validate attr a
          then return a
          else fail "Not in range"

newtype EVSFromOrchestrationAC (c0 :: Type -> Constraint) (c :: Type -> Constraint) m a = EVSFromOrchestrationAC { runEVSFromOrchestrationAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail)

instance ( Has (Orchestration EVSSupply) sig m
         , Has (State PState)            sig m
         , Has (Error EVSError)          sig m
         , CMembers Serialize c)
      => Algebra (EVS c :+: sig) (EVSFromOrchestrationAC Serialize c m) where
  alg hdl sig ctx = EVSFromOrchestrationAC $ case sig of
    L evs   -> resolveEVS evs
    R other -> alg (runEVSFromOrchestrationAC . hdl) other ctx
    where
      resolveEVS evs = case evs of
        EExogenous a@(Anything :: ExogenousAttribute c a) -> do
          v <- next (show a) \\ witnessC @Serialize @c @a
          return (ctx $> Value v)
        EExogenous a@(IntRange l r) -> do
          v <- next (show a)
          return (ctx $> Value (sampleRange l r v))
        EExogenous a@(Range    l r) -> do
          v <- next (show a)
          return (ctx $> Value (sampleRange l r v))
        where
          next attr = do
            x <- nextInstruction @EVSSupply S.get
            case x of
              Nothing -> throwError (EVSError attr "EVS supplier exhausted")
              Just  a -> return a

          sampleRange l r v = toEnum $ l' + (v `mod` (r' - l' + 1))
            where
              l' = fromEnum l
              r' = fromEnum r


instance ( Has (Orchestration EVSSupply) sig m
         , Has (State PState)            sig m
         , Has (Error EVSError)          sig m
         , CMembers HSerialize c)
      => Algebra (EVS c :+: sig) (EVSFromOrchestrationAC HSerialize c m) where
  alg hdl sig ctx = EVSFromOrchestrationAC $ case sig of
    L evs   -> resolveEVS evs
    R other -> alg (runEVSFromOrchestrationAC . hdl) other ctx
    where
      resolveEVS evs = case evs of
        EExogenous a@(Anything :: ExogenousAttribute c a)    -> do
          v <- next (show a) \\ witnessC @HSerialize @c @a
          return (ctx $> Value v)
        EExogenous a@(IntRange l r) -> do
          v <- next (show a)
          return (ctx $> Value (sampleRange l r v))
        EExogenous a@(Range    l r) -> do
          v <- next (show a)
          return (ctx $> Value (sampleRange l r v))
        where
          next attr = do
            x <- nextInstruction @EVSSupply HS.hget
            case x of
              Nothing -> throwError (EVSError attr "EVS supplier exhausted")
              Just  a -> return a

          sampleRange l r v = toEnum $ l' + (v `mod` (r' - l' + 1))
            where
              l' = fromEnum l
              r' = fromEnum r
