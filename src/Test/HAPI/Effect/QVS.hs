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
import Test.QuickCheck.Gen (Gen)
import Test.QuickCheck.GenT (MonadGen (liftGen))
import Test.HAPI.PState (PKey, PState, PStateSupports (lookUp))
import Test.HAPI.Common (Fuzzable)
import Data.Maybe (fromJust)
import Data.HList (HList (HNil), HMap,type  (:~:) (Refl))
import Data.SOP ( Proxy(Proxy), NP(..), All, hcmap )
import Test.HAPI.Args (Args, pattern (::*), Attribute (..), validate, DirectAttribute (..))
import Data.SOP.Dict (mapAll)
import Data.Serialize (Serialize)
import Test.HAPI.Effect.Orchestration (Orchestration, nextInstruction)
import Test.HAPI.Effect.Orchestration.Labels (QVSSupply)
import Data.Type.Equality (castWith, TestEquality (testEquality), apply)
import Type.Reflection ( TypeRep, typeOf, Typeable )
import Test.HAPI.Constraint (type (:>>>:), castC)
import Data.Constraint ((\\), mapDict, Dict (..))


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

qvs2Direct :: (Has (QVS c :+: State PState) sig m) => NP (QVS c m) p -> m (NP DirectAttribute p)
qvs2Direct Nil = return Nil
qvs2Direct (qvs@(QVS a) :* q) = do
  d <- case a of
    Direct (Get x) -> do
      r <- gets @PState (lookUp x)
      case r of
        Nothing -> return (Get x)
        Just v  -> return (Value v)
    _              -> Value <$> send qvs
  s <- qvs2Direct q
  return (d :* s)


newtype QVSFuzzArbitraryAC (c :: Type -> Constraint) m a = QVSFuzzArbitraryAC { runQVSFuzzArbitraryAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

instance (Algebra sig m, Members (State PState :+: GenA) sig, c :>>>: Arbitrary) => Algebra (QVS c :+: sig) (QVSFuzzArbitraryAC c m) where
  alg hdl sig ctx = QVSFuzzArbitraryAC $ case sig of
    L qvs   -> resolveQVS qvs
    R other -> alg (runQVSFuzzArbitraryAC . hdl) other ctx
    where
      resolveQVS (QVS (attr :: Attribute a)) = case attr of
        Direct (Get k)   -> do
          v <- gets @PState (lookUp k)
          return (ctx $> fromJust v)   -- TODO Exception
        Direct (Value v) -> do
          return (ctx $> v)
        Anything     -> do
          v <- liftGenA (arbitrary \\ castC @Arbitrary (Dict @(c a)))
          return (ctx $> v)
        IntRange l r -> do
          v <- liftGenA (chooseInt (l, r))
          return (ctx $> v)
        Range    l r -> do
          v <- liftGenA (chooseEnum (l, r))
          return (ctx $> v)
        AnyOf xs     -> do
          a <- oneof' (return <$> xs)
          resolveQVS (QVS a)

newtype QVSFromStdinAC (c :: Type -> Constraint) m a = QVSFromStdinAC { runQVSFromStdinAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m, c :>>>: Read) => Algebra (QVS c :+: sig) (QVSFromStdinAC c m) where
  alg hdl sig ctx = QVSFromStdinAC $ case sig of
    L qvs -> do
      liftIO $ putStrLn "Please provide input: "
      input <- liftIO $ case qvs of QVS (attr :: Attribute a) -> readAndValidate attr \\ castC @Read (Dict @(c a))
      return (ctx $> input)
    R other -> alg (runQVSFromStdinAC . hdl) other ctx
    where
      readAndValidate attr = do
        a <- readLn
        if validate attr a
          then return a
          else fail "Not in range"

newtype QVSFromOrchestrationAC (c :: Type -> Constraint) m a = QVSFromOrchestrationAC { runQVSFromOrchestrationAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail)

instance ( Has (Orchestration QVSSupply :+: State PState) sig m
         , c :>>>: Fuzzable)
      => Algebra (QVS c :+: sig) (QVSFromOrchestrationAC c m) where
  alg hdl sig ctx = QVSFromOrchestrationAC $ case sig of
    L qvs   -> resolveQVS qvs
    R other -> alg (runQVSFromOrchestrationAC . hdl) other ctx
    where
      resolveQVS (QVS attr) = case attr of
        Direct (Get k)   -> do
          v <- gets @PState (lookUp k)
          return (ctx $> fromJust v)   -- TODO Exception
        Direct (Value v) -> do
          return (ctx $> v)
        Anything     -> do
          v <- nextInstruction @QVSSupply
          return (ctx $> v)
        IntRange l r -> do
          v <- nextInstruction @QVSSupply
          return (ctx $> (l + v `mod` (r - l + 1)))
        Range    l r -> do
          v <- nextInstruction @QVSSupply   -- FIXME
          return (ctx $> v)
        AnyOf xs     -> do
          v <- nextInstruction @QVSSupply
          let a = xs !! (v `mod` length xs)
          resolveQVS (QVS a)
