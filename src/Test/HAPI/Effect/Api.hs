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

module Test.HAPI.Effect.Api where
import Test.HAPI.Api (ApiDefinition, HasHaskellDef (evalHaskell), HaskellIOCall (readOut), HasForeignDef (evalForeign), ApiName (apiName), ApiTrace (ApiTrace), ApiTraceEntry (CallOf), ApiError, apiTrace)
import Data.Kind (Type)
import Test.HAPI.Args (Args, showArgs)
import Test.HAPI.Common (Fuzzable)
import Control.Algebra (Has, Algebra (alg), type (:+:) (L, R), send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Functor (($>))
import Test.HAPI.FFI (FFIO(unFFIO))
import Data.List (intercalate)
import Control.Carrier.Writer.Strict (Writer, tell, runWriter)
import Control.Effect.Sum (Member, Members)
import Control.Effect.Trace (Trace, trace)
import Data.SOP (All)
import Control.Carrier.State.Strict (State, StateC, get, runState, execState, evalState)
import Test.HAPI.VPtr (VPtrTable)
import qualified Test.HAPI.VPtr as VP
import Control.Effect.Fresh ( Fresh )
import Control.Effect.Error ( Error )

-- | Wrapper to the original Api
data Api (api :: ApiDefinition) (m :: Type -> Type) a where
  MkCall :: (ApiName api, All Show p) =>  api p a -> Args p -> Api api m a

mkCall :: (Has (Api api) sig m, Fuzzable a, ApiName api, All Show p) => api p a -> Args p -> m a
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

newtype ApiFFIAC (api :: ApiDefinition) m a = ApiFFIAC { runApiFFIAC :: StateC VPtrTable m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiFFI :: forall api m a . Monad m => ApiFFIAC api m a -> m a
runApiFFI = evalState VP.empty . runApiFFIAC

instance (Algebra sig m, HasForeignDef api, Members (Fresh :+: Error ApiError :+: Writer (ApiTrace api) :+: Trace) sig, MonadIO m) => Algebra (Api api :+: sig) (ApiFFIAC api m) where
  alg hdl sig ctx = ApiFFIAC $ case sig of
    L (MkCall call args) -> do
      tell $ apiTrace $ CallOf call args
      trace $ apiName call <> showArgs args
      vt <- get @VPtrTable
      r <- evalForeign call args
      return (ctx $> r)
    R other -> alg (runApiFFIAC . hdl) (R other) ctx

-- | Logging
newtype ApiTracingAC underlying (api :: ApiDefinition) m a = ApiTracingAC {
  runApiTracingAC :: (forall m b. (Monad m) => underlying api m b -> m b) -> (forall m b. (Monad m) => m b -> underlying api m b) -> m a
}

-- runApiTracing :: forall api underlying m a. (forall m b. (Monad m) => underlying api m b -> m b) -> (forall m b. (Monad m) => m b -> underlying api m b) -> ApiTracingAC underlying api m a -> m a
-- runApiTracing f u (ApiTracingAC c) = c f u

-- instance (Algebra (Api api :+: sig) (underlying api m),
--           Algebra sig m,
--           Members (Writer (ApiTrace api) :+: Trace) sig,
--           MonadIO m)
--           => Algebra (Api api :+: sig) (ApiTracingAC underlying api m) where
--   alg hdl sig ctx = ApiTracingAC $ \u c -> case sig of
--     L api@(MkCall f args) -> do
--       u (alg (c . runApiTracing u c . hdl) (L api) ctx)
--     R other -> alg (runApiTracing u c . hdl) other ctx


-- instance (Functor (underlying api m), Functor m) => Functor (ApiTracingAC underlying api m) where
--   fmap f (ApiTracingAC ac) = ApiTracingAC $ \u c -> fmap f (ac u c)

-- instance (Applicative (underlying api m), Applicative m) => Applicative (ApiTracingAC underlying api m) where
--   pure a  = ApiTracingAC $ \_ _ -> pure a
--   (ApiTracingAC f) <*> (ApiTracingAC a) = ApiTracingAC $ \u c -> f u c <*> a u c

-- instance (Monad (underlying api m), Monad m) => Monad (ApiTracingAC underlying api m) where
--   (ApiTracingAC a) >>= f = ApiTracingAC $ \u c -> a u c >>= (runApiTracing u c . f)

