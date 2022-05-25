{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Test.HAPI.Effect.Orchestration where
import Data.Kind (Type, Constraint)
import Test.HAPI.Common (Fuzzable)
import Control.Algebra
  ( Algebra(alg), type (:+:)(L, R), send, Has )
import Data.ByteString (ByteString)
import Data.Functor (($>))
import Control.Effect.Error (Error, throwError, liftEither)
import Control.Effect.Sum (Members)
import Control.Effect.State (State (Get, Put), state, put)
import Data.Serialize (Serialize)
import Control.Carrier.Error.Church (runError, ErrorC)
import Control.Carrier.State.Church (runState, StateC, gets)

import qualified Data.Serialize as S
import Test.HAPI.Effect.Orchestration.Labels (QVSSupply, LabelConsumeDir (..))
import Test.HAPI.Util.ByteSupplier (ByteSupplier (eatBytes), BiDir, eatForward, EQSupplier)
import Data.Either.Combinators (mapLeft)
import Test.HAPI.Effect.Eff
import Text.Printf (printf)

data Orchestration label (m :: Type -> Type) a where
  NextInstruction :: (Serialize a, Show a) => S.Get a -> Orchestration label m (Maybe a)

nextInstruction :: forall label a c sig m. (Has (Orchestration label) sig m, Serialize a, Show a) => S.Get a -> m (Maybe a)
nextInstruction = send . NextInstruction @a @label

newtype OrchestrationError = OrchestrationError String

instance Show OrchestrationError where
  show (OrchestrationError err) = "Orchestration Error: " <> err

newtype OrchestrationViaBytesAC label supply m a = OrchestrationViaBytesAC { runOrchestrationViaBytesAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail)

type OrchestrationViaBytesFC label supply m a
  = OrchestrationViaBytesAC label supply m a

runOrchestrationViaBytes :: forall label supply a sig m. (Has (State EQSupplier) sig m)
                         => OrchestrationViaBytesFC label supply m a
                         -> m a
runOrchestrationViaBytes = runOrchestrationViaBytesAC

instance ( Alg sig m
        --  , Members (Error OrchestrationError) sig
         , ByteSupplier BiDir supply
         , LabelConsumeDir label BiDir
         , Members (State supply) sig)
      => Algebra (Orchestration label :+: sig) (OrchestrationViaBytesAC label supply m) where
  alg hdl sig ctx = OrchestrationViaBytesAC $ case sig of
    L (NextInstruction get) -> do
      e <- gets @supply (eatBytes (labelConsumeDir @label) get)
      -- debug $ printf "%s: e = %s" (show 'alg) (show e)
      case e of
        Left err          -> return (ctx $> Nothing)
        Right (a, supply) -> put supply >> return (ctx $> Just a)
    R other    -> alg (runOrchestrationViaBytesAC . hdl) other ctx
