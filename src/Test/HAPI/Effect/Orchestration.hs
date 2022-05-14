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
import Test.HAPI.Util.ByteSupplier (ByteSupplier (eatBytes), BiDir, BiDirBS, eatForward)
import Data.Either.Combinators (mapLeft)

data Orchestration label (m :: Type -> Type) a where
  NextInstruction :: (Serialize a) => Orchestration label m a

nextInstruction :: forall label a c sig m. (Has (Orchestration label) sig m, Serialize a) => m a
nextInstruction = send (NextInstruction @a @label)

newtype OrchestrationError = OrchestrationError String

instance Show OrchestrationError where
  show (OrchestrationError err) = "Orchestration Error: " <> err

newtype OrchestrationViaBytesAC label supply m a = OrchestrationViaBytesAC { runOrchestrationViaBytesAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail)

type OrchestrationViaBytesFC label supply m a
  = OrchestrationViaBytesAC label supply
    (ErrorC OrchestrationError m)
    a

runOrchestrationViaBytes :: forall label supply a sig m. (Has (State BiDirBS) sig m)
                         => (OrchestrationError -> m a)
                         -> OrchestrationViaBytesFC label supply m a
                         -> m a
runOrchestrationViaBytes err n
  = runError err return
  $ runOrchestrationViaBytesAC @label
  $ n

instance ( Algebra sig m
         , Members (Error OrchestrationError) sig
         , ByteSupplier BiDir supply
         , LabelConsumeDir label BiDir
         , Members (State supply) sig)
      => Algebra (Orchestration label :+: sig) (OrchestrationViaBytesAC label supply m) where
  alg hdl sig ctx = OrchestrationViaBytesAC $ case sig of
    L (NextInstruction :: Orchestration label n a) -> do
      e <- mapLeft (OrchestrationError . show) <$> gets @supply (eatBytes (labelConsumeDir @label) (S.get @a))
      (a, supply) <- liftEither e
      put supply
      return (ctx $> a)
    R other    -> alg (runOrchestrationViaBytesAC . hdl) other ctx
