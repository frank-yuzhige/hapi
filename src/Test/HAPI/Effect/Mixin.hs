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

module Test.HAPI.Effect.Mixin (
    module Control.Algebra
  , EnvA (..)
  , EnvAC (..)
  , EnvCtx
  , Has
  , Env
  , envCtx
  , debug
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

newtype EnvAC ctx m a = EnvAC { runEnvAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m) => Algebra (EnvA :+: sig) (EnvAC ctx m) where
  alg hdl sig ctx = EnvAC $ case sig of
    L EnvCtx      -> return $ ctx $> ()
    L (Debug msg) -> do
      liftIO $ hPutStrLn stderr (printf "[DEBUG]: %s" msg)
      return $ ctx $> ()
    R other       -> alg (runEnvAC . hdl) other ctx

-- Mixin

type Has eff sig m = (A.Has (eff :+: EnvA) sig m)

type Env sig m = A.Has EnvA sig m

-- Sender

envCtx :: Env sig m => m EnvCtx
envCtx = send EnvCtx

debug :: Env sig m => String -> m ()
debug = send . Debug
