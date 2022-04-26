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
import qualified Data.Serialize as S
import Data.Functor (($>))
import Control.Effect.Error (Error, throwError)
import Control.Effect.Sum (Members)
import Control.Effect.Labelled (HasLabelled, sendLabelled, runLabelled, Labelled)
import Control.Effect.State (State (Get, Put))
import Data.Serialize (Serialize)
import Control.Carrier.Error.Church (runError, ErrorC)
import Control.Carrier.State.Church (runState, StateC)

data Orchestration label (m :: Type -> Type) a where
  NextInstruction :: (Serialize a) => Orchestration label m a

nextInstruction :: forall label a c sig m. (Has (Orchestration label) sig m, Serialize a) => m a
nextInstruction = send (NextInstruction @a @label)

newtype OrchestrationError = CerealError String

instance Show OrchestrationError where
  show (CerealError err) = "Cereal Error: " <> err

newtype OrchestrationViaBytesAC label m a = OrchestrationViaBytesAC { runOrchestrationViaBytesAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail)

type OrchestrationViaBytesFC label m a
  = OrchestrationViaBytesAC label
    (Labelled label
      (StateC ByteString)
      (ErrorC OrchestrationError m))
    a

runOrchestrationViaBytes :: forall label a sig m. Algebra sig m
                         => (OrchestrationError -> m a)
                         -> ByteString
                         -> OrchestrationViaBytesFC label m a
                         -> m a
runOrchestrationViaBytes err bs n
  = runError err return
  $ runState (\_ a -> return a) bs
  $ runLabelled @label
  $ runOrchestrationViaBytesAC @label
  $ n
instance ( Has       (Error OrchestrationError) sig m
         , HasLabelled label (State ByteString) sig m)
         => Algebra (Orchestration label :+: sig) (OrchestrationViaBytesAC label m) where
  alg hdl sig ctx = OrchestrationViaBytesAC $ case sig of
    L (NextInstruction :: Orchestration label n a) -> do
      bs <- sendLabelled @label $ Get @ByteString
      case S.runGetState (S.get @a) bs 0 of
        Left err -> throwError @OrchestrationError $ CerealError err
        Right (a, bs') -> do
          sendLabelled @label $ Put @ByteString bs'
          return (ctx $> a)
    R other    -> alg (runOrchestrationViaBytesAC . hdl) other ctx
