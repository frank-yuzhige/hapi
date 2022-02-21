{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
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

{-
Quantified Value Generation Effect
-}

module Test.HAPI.QVS where
import Control.Algebra (Algebra (alg), type (:+:) (L, R), Has, send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Test.HAPI.GenT (GenAC(runGenAC), GenA (LiftGenA), liftGenA)
import Test.QuickCheck (Arbitrary(arbitrary), chooseInt, chooseEnum)
import Data.Kind (Constraint, Type)
import Data.Functor (($>))
import Data.Data (Proxy)
import Control.Carrier.State.Church (StateC, get)
import Control.Effect.State (State)
import Control.Effect.Sum (Member)
import Test.HAPI.DataType (TypeSpec, GetSpecCons, TyMember, WFTypeSpec, GetSpecTypes, WFTypeSpec_, TyIn)
import Test.QuickCheck.Gen (Gen)

-- Quantified Value Supplier
data QVS (spec :: Type) (m :: Type -> Type) a where
  IntRange  :: (TyIn Int spec)
            => Int -> Int -> QVS spec m Int
  Range     :: (TyIn a spec, Ord a, Enum a)
            => a   -> a   -> QVS spec m a

validate :: QVS ts m a -> ts -> a -> Bool
validate qvs state a = case qvs of
  IntRange l r -> l <= a && a <= r
  Range    l r -> l <= a && a <= r

respec :: (d a, WFTypeSpec (TypeSpec ts d)) => QVS (TypeSpec ts c) m a -> QVS (TypeSpec ts d) m a
respec (IntRange a b) = IntRange a b
respec (Range    a b) = Range    a b

newtype QVSFuzzArbitraryCA s m a = QVFuzzArbitraryCA { runQVSFuzzArbitraryCA :: GenAC m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

instance (Algebra sig m, Member (State spec) sig) => Algebra (QVS spec :+: sig) (QVSFuzzArbitraryCA spec m) where
  alg hdl sig ctx = QVFuzzArbitraryCA $ case sig of
    L qvs -> case qvs of
      IntRange l r -> do
        a <- liftGenA (chooseInt (l, r))
        return (ctx $> a)
      Range    l r -> do
        a <- liftGenA (chooseEnum (l, r))
        return (ctx $> a)
    R other -> alg (runQVSFuzzArbitraryCA . hdl) (R other) ctx

newtype QVSFromStdin s m a = QVFromStdin { runQVSFromStdin :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m, Read ~ GetSpecCons spec) => Algebra (QVS spec :+: sig) (QVSFromStdin spec m) where
  alg hdl sig ctx = case sig of
    L qvs -> do
      liftIO (putStrLn "Please provide input: ")
      input <- liftIO $ case qvs of
         IntRange n i  -> readLn
         Range    a a' -> readLn
      return (ctx $> input)
    R other -> QVFromStdin $ alg (runQVSFromStdin . hdl) other ctx
