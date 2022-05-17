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

module Test.HAPI.Effect.Entropy where
import Data.Kind (Type)
import Control.Algebra (Algebra, type (:+:) (L, R), Has, send)
import Test.HAPI.Effect.Orchestration (Orchestration, nextInstruction, OrchestrationError, runOrchestrationViaBytes, OrchestrationViaBytesFC)
import Test.HAPI.Effect.Orchestration.Labels (EntropySupply)
import Control.Effect.Sum (Members)
import Control.Effect.Labelled (Algebra(alg))
import Data.Int (Int8)
import Data.Functor (($>))
import Data.ByteString (ByteString)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (..))
import Control.Carrier.Error.Either (runError, liftEither)
import Data.Either.Combinators (mapLeft)

data EntropySupplier (m :: Type -> Type) a where
  GetEntropy :: Int -> EntropySupplier m (Maybe Int)

getEntropy :: Has EntropySupplier sig m => Int -> m (Maybe Int)
getEntropy = send . GetEntropy

newtype EntropyAC m a = EntropyAC { runEntropyAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail)

instance ( Algebra sig m
         , MonadFail m
         , Members (Orchestration EntropySupply) sig)
         => Algebra (EntropySupplier :+: sig) (EntropyAC m) where
  alg hdl sig ctx = EntropyAC $ case sig of
    L (GetEntropy r)
      | r <= 0    -> fatalError 'alg FATAL_ERROR
        "Attempt to get an negative entropy value. If you are not using the internal EntropySupplier API, please file this as a BUG."
      | r == 1    -> return (ctx $> Just 0)
      | otherwise -> do
        mi <- runError @OrchestrationError (nextInstruction @EntropySupply @Int)
        case mi of
          Left _  -> return (ctx $> Nothing)
          Right i -> return (ctx $> Just (i `mod` r))
    R other -> alg (runEntropyAC . hdl) other ctx
