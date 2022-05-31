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
import Data.Word (Word8)
import Test.HAPI.Effect.Eff
import qualified Data.Serialize as S
import Control.Effect.State (State, modify, get)
import Text.Printf (printf)
import Control.Monad (when)
import Data.Maybe (isNothing)

newtype EntropyCounter = EntropyCounter Int
  deriving (Eq, Ord, Num, Real, Enum, Integral, Show)

data EntropySupplier (m :: Type -> Type) a where
  GetEntropy :: Int -> EntropySupplier m (Maybe Int)

getEntropy :: Has EntropySupplier sig m => Int -> m (Maybe Int)
getEntropy = send . GetEntropy

maxEntropyStep :: EntropyCounter
maxEntropyStep = 2048

newtype EntropyAC m a = EntropyAC { runEntropyAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail)

instance ( Alg sig m
         , Members (Orchestration EntropySupply) sig
         , Members (State EntropyCounter) sig)
         => Algebra (EntropySupplier :+: sig) (EntropyAC m) where
  alg hdl sig ctx = EntropyAC $ case sig of
    L (GetEntropy r)
      | r <= 0    -> fatalError 'alg FATAL_ERROR
        "Attempt to get an negative entropy value. If you are not using the internal EntropySupplier API, please file this as a BUG."
      -- | r == 1  -> do
        -- modify @EntropyCounter (+1)
        -- step <- get @EntropyCounter
        -- return (ctx $> if step > maxEntropyStep then Just 0 else Nothing)
      -- We use entropy bytestring's length to indicate how long the traversal is.
      -- So even if we only have one out edge, we still eat a byte to avoid infinite loop.
      | otherwise -> do
        modify @EntropyCounter (+1)
        step <- get @EntropyCounter
        if step > maxEntropyStep
          then return (ctx $> Nothing)
          else do
            mi <- nextInstruction @EntropySupply S.getWord8
            -- when (isNothing mi) (debug $ printf "%s: exhaust due to getter error entropy = %s" (show 'alg) (show step))
            return (ctx $> ((\i -> fromIntegral i `mod` r) <$> mi))
    R other -> alg (runEntropyAC . hdl) other ctx
