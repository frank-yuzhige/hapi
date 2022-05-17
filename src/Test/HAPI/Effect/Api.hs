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
{-# LANGUAGE TemplateHaskell #-}

module Test.HAPI.Effect.Api where
import Test.HAPI.Api (ApiDefinition, HasHaskellDef (evalHaskell), HaskellIOCall (readOut), HasForeignDef (evalForeign), ApiName (apiName, showApiFromPat), ApiError, HasForeign, runForeign)
import Data.Kind (Type)
import Test.HAPI.Args (Args, args2Pat)
import Test.HAPI.Common (Fuzzable)
import Control.Algebra (Has, Algebra (alg), type (:+:) (L, R), send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Functor (($>))
import Data.List (intercalate)
import Control.Carrier.Writer.Strict (Writer, tell, runWriter)
import Control.Effect.Sum (Member, Members)
import Control.Effect.Trace (Trace, trace)
import Data.SOP (All)
import Control.Carrier.State.Strict (State, StateC, get, runState, execState, evalState)
import Test.HAPI.VPtr (VPtrTable)
import qualified Test.HAPI.VPtr as VP
import Control.Effect.Fresh ( Fresh )
import Control.Effect.Error ( Error, throwError )
import Test.HAPI.ApiTrace (ApiTrace, apiTrace, ApiTraceEntry (..))
import Control.Concurrent (newEmptyMVar, forkOS, putMVar, readMVar, takeMVar, newMVar)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR, HAPI_BUG))
import Text.Printf (printf)

-- | Wrapper to the original Api
data Api (api :: ApiDefinition) (m :: Type -> Type) a where
  MkCall :: (ApiName api, All Fuzzable p, Fuzzable a)
         => api p a -> Args p -> Api api m a

mkCall :: (Has (Api api) sig m, Fuzzable a, ApiName api, All Fuzzable p) => api p a -> Args p -> m a
mkCall = (send .) . MkCall

-- | Encode api call's type into its underlying interpretation to ensure functional dependency for Algebra holds
newtype ApiAC (api :: ApiDefinition) m a = ApiAC { runApiAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApi :: ApiAC api m a -> m a
runApi = runApiAC

-- | If the api call can map to relevant haskell functions, then it can be interpreted
instance (Algebra sig m, HasHaskellDef api) => Algebra (Api api :+: sig) (ApiAC api m) where
  alg hdl sig ctx = ApiAC $ case sig of
    L (MkCall call args) -> return (ctx $> evalHaskell call args)
    R other              -> alg (runApiAC . hdl) other ctx


-- | Haskell IO Orchestration

newtype ApiIOAC (api :: ApiDefinition) m a = ApiIOAC { runApiIOAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiIO :: ApiIOAC api m a -> m a
runApiIO = runApiIOAC

instance (Algebra sig m, MonadIO m, MonadFail m, HaskellIOCall api) => Algebra (Api api :+: sig) (ApiIOAC api m) where
  alg hdl sig ctx = ApiIOAC $ case sig of
    L (MkCall call args) -> do
      liftIO $ putStrLn $ apiName call
      out <- liftIO (readOut call <$> getLine)
      case out of
        Nothing -> fail "Parse error"
        Just o  -> return (ctx $> o)
    R other -> alg (runApiIOAC . hdl) other ctx


-- | Foreign

newtype ApiFFIAC (api :: ApiDefinition) m a = ApiFFIAC { runApiFFIAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiFFI :: forall api m a . Monad m => ApiFFIAC api m a -> m a
runApiFFI = runApiFFIAC

instance ( Algebra sig m
         , HasForeignDef api
         , HasForeign sig m
         , MonadIO m)
         => Algebra (Api api :+: sig) (ApiFFIAC api m) where
  alg hdl sig ctx = ApiFFIAC $ case sig of
    L (MkCall call args) -> do
      liftIO $ putStrLn $ showApiFromPat call (args2Pat args)
      r <- evalForeign call args
      return (ctx $> r)
    R other -> alg (runApiFFIAC . hdl) other ctx

-- | Trace

newtype ApiTraceAC (api :: ApiDefinition) m a = ApiTraceAC { runApiTraceAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiTrace :: forall api m a . Monad m => ApiTraceAC api m a -> m a
runApiTrace = runApiTraceAC

instance ( Algebra sig m
         , HasForeignDef api
         , MonadIO m
         , MonadFail m)
         => Algebra (Api api :+: sig) (ApiTraceAC api m) where
  alg hdl sig ctx = ApiTraceAC $ case sig of
    L (MkCall call args) -> do
      fatalError 'alg HAPI_BUG $ printf "HAPI is trying to call an API via its foreign definition during trace mode!"
    R other -> alg (runApiTraceAC . hdl) other ctx
