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
{-# LANGUAGE StandaloneDeriving #-}

{-
Quantified Value Generation Effect
-}

module Test.HAPI.Effect.QVS where
import Control.Algebra (Algebra (alg), type (:+:) (L, R), Has, send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Test.HAPI.Effect.Gen (GenAC(runGenAC), GenA (LiftGenA), liftGenA, oneof, oneof')
import Test.QuickCheck (Arbitrary(arbitrary), chooseInt, chooseEnum)
import Data.Kind (Constraint, Type)
import Data.Functor (($>))
import Control.Carrier.State.Church (StateC, get)
import Control.Effect.State ( State, gets )
import Control.Effect.Sum (Member, Members)
import Test.HAPI.DataType (TypeSpec, GetSpecCons, TyMember, WFTypeSpec, GetSpecTypes, WFTypeSpec_, TyIn)
import Test.QuickCheck.Gen (Gen)
import Test.QuickCheck.GenT (MonadGen (liftGen))
import Test.HAPI.PState (PKey, PState, PStateSupports (lookUp))
import Test.HAPI.Common (Fuzzable)
import Data.Maybe (fromJust)
import Data.HList (HList (HNil), HMap,type  (:~:) (Refl))
import Data.SOP
import Test.HAPI.Args (Args, pattern (::*), Attribute (Value, Anything, IntRange, Range, Get, AnyOf), validate)
import Data.SOP.Dict (mapAll, Dict (Dict))
import Data.Serialize (Serialize)
import Test.HAPI.Effect.Orchestration (Orchestration, readFromOrchestration)
import Data.Type.Equality (castWith, TestEquality (testEquality), apply)
import Type.Reflection ( TypeRep, typeOf, Typeable )


-- Quantified Value Supplier
data QVS (c :: Type -> Constraint) (m :: Type -> Type) a where
  QVS :: (c a) => Attribute a -> QVS c m a

-- | Convert attribute to QVS
attributes2QVSs :: forall c p m. (All c p) => NP Attribute p -> NP (QVS c m) p
attributes2QVSs = hcmap (Proxy @c) QVS

-- | Generate values in HList
qvs2m :: (Has (QVS c) sig m) => NP (QVS c m) p -> m (Args p)
qvs2m Nil = return Nil
qvs2m (qvs :* q) = do
  a <- send qvs
  s <- qvs2m q
  return (a ::* s)



newtype QVSFuzzArbitraryAC s m a = QVSFuzzArbitraryAC { runQVSFuzzArbitraryAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

instance (Algebra sig m, Members (State PState :+: GenA) sig) => Algebra (QVS Arbitrary :+: sig) (QVSFuzzArbitraryAC spec m) where
  alg hdl sig ctx = QVSFuzzArbitraryAC $ case sig of
    L qvs   -> resolveQVS qvs
    R other -> alg (runQVSFuzzArbitraryAC . hdl) other ctx
    where
      resolveQVS (QVS attr) = case attr of
        Value v      -> do
          return (ctx $> v)
        Anything     -> do
          v <- liftGenA arbitrary
          return (ctx $> v)
        IntRange l r -> do
          v <- liftGenA (chooseInt (l, r))
          return (ctx $> v)
        Range    l r -> do
          v <- liftGenA (chooseEnum (l, r))
          return (ctx $> v)
        Get k        -> do
          v <- gets @PState (lookUp k)
          return (ctx $> fromJust v)   -- TODO Exception
        AnyOf xs     -> do
          a <- oneof' (return <$> xs)
          resolveQVS (QVS a)

newtype QVSFromStdinAC m a = QVSFromStdinAC { runQVSFromStdinAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m) => Algebra (QVS Read :+: sig) (QVSFromStdinAC m) where
  alg hdl sig ctx = QVSFromStdinAC $ case sig of
    L qvs -> do
      liftIO $ putStrLn "Please provide input: "
      input <- liftIO $ case qvs of QVS attr -> readAndValidate attr
      return (ctx $> input)
    R other -> alg (runQVSFromStdinAC . hdl) other ctx
    where
      readAndValidate attr = do
        a <- readLn
        if validate attr a
          then return a
          else fail "Not in range"

newtype QVSFromOrchestrationAC m a = QVSFromOrchestrationAC { runQVSFromOrchestrationAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail)

instance (Algebra sig m, Member Orchestration sig) => Algebra (QVS Fuzzable :+: sig) (QVSFromOrchestrationAC m) where
  alg hdl sig ctx = QVSFromOrchestrationAC $ case sig of
    L (QVS (attr :: Attribute a)) -> do
      x <- readFromOrchestration @a
      return (ctx $> x)
    R other -> alg (runQVSFromOrchestrationAC . hdl) other ctx
