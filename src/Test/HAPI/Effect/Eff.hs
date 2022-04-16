{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Test.HAPI.Effect.Eff (
    module Control.Algebra
  , EnvA (..)
  , EnvAC (..)
  , EnvCtx
  , Alg
  , Eff
  , envCtx
  , debug
  , runEnv
) where
import Data.Kind (Type)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Functor (($>))
import System.IO (hPutStrLn, stderr)
import Text.Printf (printf)

import Control.Algebra hiding (Has)
import qualified Control.Algebra as A


type EnvCtx = ()

data EnvA (m :: Type -> Type) a where
  EnvCtx ::           EnvA m EnvCtx
  Debug  :: String -> EnvA m ()

newtype EnvAC m a = EnvAC { runEnvAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m) => Algebra (EnvA :+: sig) (EnvAC m) where
  alg hdl sig ctx = EnvAC $ case sig of
    L EnvCtx      -> return $ ctx $> ()
    L (Debug msg) -> do
      liftIO $ hPutStrLn stderr (printf "[DEBUG]: %s" msg)
      return $ ctx $> ()
    R other       -> alg (runEnvAC . hdl) other ctx

-- Mixin

-- | Mixin of @Has@ in @Control.Algebra@, adds extra @EnvA@ to allow global operations
type Eff eff sig m = (A.Has eff sig m, A.Has EnvA sig m)

-- | Mixin of @Algebra@ in @Control.Algebra@, adds extra @EnvA@ to allow global operations
type Alg sig m = A.Has EnvA sig m

-- Sender

envCtx :: Alg sig m => m EnvCtx
envCtx = send EnvCtx

debug :: Alg sig m => String -> m ()
debug = send . Debug

-- runner

runEnv :: MonadIO m => EnvAC m a -> m a
runEnv = runEnvAC
