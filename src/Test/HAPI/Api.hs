{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.HAPI.Api where

import Control.Algebra (Has, alg, send, Algebra, (:+:) (L, R), Handler)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Carrier.State.Church (StateC(..), put, execState)
import Control.Carrier.Cull.Church (MonadPlus)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.Writer.Strict (WriterC, tell)
import Data.Functor (($>))
import Data.Void (Void)
import Data.Kind (Constraint)
import Text.Read (readMaybe)
import Control.Effect.Labelled (Labelled (Labelled), runLabelled)
import Test.HAPI.FFI (FFIO(FFIO, unFFIO))
import Control.Monad.Trans.Identity (IdentityT (runIdentityT))


type ApiDefinition = (* -> *) -> * -> *

class HasHaskellDef (api :: ApiDefinition) where
  evalHaskell :: api m a -> a

class HasForeignDef (api :: ApiDefinition) where
  evalForeign :: api m a -> FFIO a

class HaskellIOCall (api :: ApiDefinition) where
  showArgs :: api m a -> String
  readOut :: api m a -> String -> Maybe a

class RpcCall (api :: ApiDefinition) where
  makeRpcCall :: api m a -> undefined


-- | Encode api call's type into its underlying interpretation to ensure functional dependency for Algebra holds
newtype ApiAC (api :: ApiDefinition) m a = ApiAC { runApiAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApi :: ApiAC api m a -> m a
runApi = runApiAC

-- | If the api call can map to relevant haskell functions, then it can be interpreted
instance (Algebra sig m, HasHaskellDef api) => Algebra (api :+: sig) (ApiAC api m) where
  alg hdl sig ctx = ApiAC $ case sig of
    L call -> return (ctx $> evalHaskell call)
    R other -> alg (runApiAC . hdl) other ctx


-- | Haskell IO Orchestration

newtype ApiIOAC (api :: ApiDefinition) m a = ApiIOAC { runApiIOAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiIO :: ApiIOAC api m a -> m a
runApiIO = runApiIOAC

instance (Algebra sig m, MonadIO m, MonadFail m, HaskellIOCall api) => Algebra (api :+: sig) (ApiIOAC api m) where
  alg hdl sig ctx = ApiIOAC $ case sig of
    L call -> do
      liftIO $ putStrLn $ showArgs call
      out <- liftIO (readOut call <$> getLine)
      case out of
        Nothing -> fail "Parse error"
        Just o  -> return (ctx $> o)
    R other -> alg (runApiIOAC . hdl) other ctx


-- | Foreign

newtype ApiFFIAC (api :: ApiDefinition) m a = ApiFFIAC { runApiFFIAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiFFI :: ApiFFIAC api m a -> m a
runApiFFI = runApiFFIAC

instance (Algebra sig m, MonadIO m, HasForeignDef api) => Algebra (api :+: sig) (ApiFFIAC api m) where
  alg hdl sig ctx = ApiFFIAC $ case sig of
    L call  -> do
      r <- liftIO $ unFFIO $ evalForeign call
      return (ctx $> r)
    R other -> alg (runApiFFIAC . hdl) other ctx
