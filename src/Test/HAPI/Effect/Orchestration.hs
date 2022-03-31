{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.HAPI.Effect.Orchestration where
import Data.Kind (Type)
import Test.HAPI.Common (Fuzzable)
import Control.Algebra
  ( Algebra(alg), type (:+:)(L, R), send, Has )
import Data.ByteString (ByteString)
import Control.Carrier.State.Strict (StateC, get, put)
import qualified Data.Serialize as S
import Data.Functor (($>))

data Orchestration (m :: Type -> Type) a where
  ReadFromOrchestration :: (Fuzzable a) => Orchestration m a

readFromOrchestration :: forall a sig m. (Has Orchestration sig m, Fuzzable a) => m a
readFromOrchestration = send ReadFromOrchestration

newtype OrchestrationViaBytesAC m a = OrchestrationViaBytesAC { runOrchestrationViaBytesAC :: StateC ByteString m a }
  deriving (Functor, Applicative, Monad)

instance (Algebra sig m, MonadFail m) => Algebra (Orchestration :+: sig) (OrchestrationViaBytesAC m) where
  alg hdl sig ctx = OrchestrationViaBytesAC $ case sig of
    L (ReadFromOrchestration :: Orchestration n a) -> do
      bs <- get @ByteString
      case S.runGetState (S.get @a) bs 0 of
        Left err -> fail err
        Right (a, bs') -> do
          put @ByteString bs'
          return (ctx $> a)
    R other    -> alg (runOrchestrationViaBytesAC . hdl) (R other) ctx
