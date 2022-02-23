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
  Any       :: (TyIn t spec)
            => QVS spec m t
  IntRange  :: (TyIn Int spec)
            => Int -> Int -> QVS spec m Int
  Range     :: (TyIn a spec, Ord a, Enum a)
            => a   -> a   -> QVS spec m a

newtype QVSFuzzArbitraryCA s m a = QVFuzzArbitraryCA { runQVSFuzzArbitraryCA :: GenAC m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

instance (Algebra sig m, Member (State spec) sig, Arbitrary ~ GetSpecCons spec) => Algebra (QVS spec :+: sig) (QVSFuzzArbitraryCA spec m) where
  alg hdl sig ctx = QVFuzzArbitraryCA $ case sig of
    L qvs -> case qvs of
      Any          -> do
        a <- liftGenA arbitrary
        return (ctx $> a)
      IntRange l r -> do
        a <- liftGenA (chooseInt (l, r))
        return (ctx $> a)
      Range    l r -> do
        a <- liftGenA (chooseEnum (l, r))
        return (ctx $> a)
    R other -> alg (runQVSFuzzArbitraryCA . hdl) (R other) ctx

newtype QVSFromStdin s m a = QVSFromStdin { runQVSFromStdin :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m, Read ~ GetSpecCons spec) => Algebra (QVS spec :+: sig) (QVSFromStdin spec m) where
  alg hdl sig ctx = case sig of
    L qvs -> do
      liftIO (putStrLn "Please provide input: ")
      input <- liftIO $ case qvs of
         Any         -> readAndValidate qvs
         IntRange {} -> readAndValidate qvs
         Range    {} -> readAndValidate qvs
      return (ctx $> input)
    R other -> QVSFromStdin $ alg (runQVSFromStdin . hdl) other ctx
    where
      readAndValidate :: Read a => QVS spec m' a -> IO a
      readAndValidate qvs = do
        a <- readLn
        if validate qvs a
          then return a
          else fail "Not in range"


validate :: QVS ts m a -> a -> Bool
validate qvs a = case qvs of
  Any          -> True
  IntRange l r -> l <= a && a <= r
  Range    l r -> l <= a && a <= r

respec :: (d a, WFTypeSpec (TypeSpec ts d)) => QVS (TypeSpec ts c) m a -> QVS (TypeSpec ts d) m a
respec Any            = Any
respec (IntRange a b) = IntRange a b
respec (Range    a b) = Range    a b
