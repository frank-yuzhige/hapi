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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.Effect.Api where
import Test.HAPI.Api (ApiDefinition, HasHaskellDef (evalHaskell), HaskellIOCall (readOut), HasForeignDef (evalForeign), ApiName (..), ApiError (..), HasForeign, runForeign)
import Data.Kind (Type, Constraint)
import Test.HAPI.Args (Args, args2Pat, DirectAttribute, DirAttributes, evalDirects, Attribute)
import Test.HAPI.Common (Fuzzable)
import Control.Algebra (Has, Algebra (alg), type (:+:) (L, R), send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Functor (($>))
import Data.List (intercalate)
import Control.Carrier.Writer.Strict (Writer, tell, runWriter)
import Control.Effect.Sum (Member, Members)
import Control.Effect.Trace (Trace, trace)
import Data.SOP (All)
import Control.Carrier.State.Strict (State, StateC, get, runState, execState, evalState, modify)
import Test.HAPI.VPtr (VPtrTable)
import qualified Test.HAPI.VPtr as VP
import Control.Effect.Fresh ( Fresh )
import Control.Effect.Error ( Error, throwError )
import Test.HAPI.ApiTrace.Core ( ApiTrace, traceCall )
import Control.Concurrent (newEmptyMVar, forkOS, putMVar, readMVar, takeMVar, newMVar)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR, HAPI_BUG))
import Text.Printf (printf)
import Test.HAPI.PState (PState, PKey, record)
import Test.HAPI.Effect.Eff (Alg, debug)

-- | Wrapper to the original Api
data Api (api :: ApiDefinition) (c :: Type -> Constraint) (m :: Type -> Type) a where
  MkCall   :: (ApiName api, All Fuzzable p, Fuzzable a, All c p, c a)
           => PKey a -> api p a -> DirAttributes c p -> Api api c m ()

mkCall :: forall c api sig m p a. (Has (Api api c) sig m, ApiName api, All Fuzzable p, Fuzzable a, All c p, c a)
       => PKey a -> api p a -> DirAttributes c p -> m ()
mkCall k f a = send $ MkCall @_ @_ @_ @c k f a

-- | Haskell IO Orchestration

newtype ApiIOAC (api :: ApiDefinition) (c :: Type -> Constraint)  m a = ApiIOAC { runApiIOAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiIO :: ApiIOAC api c m a -> m a
runApiIO = runApiIOAC

instance ( Algebra sig m
         , Has (State PState) sig m
         , MonadIO m
         , MonadFail m
         , HaskellIOCall api)
      => Algebra (Api api c :+: sig) (ApiIOAC api c m) where
  alg hdl sig ctx = ApiIOAC $ case sig of
    L (MkCall k call args) -> do
      liftIO $ putStrLn $ apiName call
      out <- liftIO (readOut call <$> getLine)
      case out of
        Nothing -> fail "Parse error"
        Just o  -> do
          modify @PState (record k o)
          return (ctx $> ())
    R other -> alg (runApiIOAC . hdl) other ctx


-- | Foreign

newtype ApiFFIAC (api :: ApiDefinition) (c :: Type -> Constraint) m a = ApiFFIAC { runApiFFIAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiFFI :: forall api c m a. Monad m => ApiFFIAC api c m a -> m a
runApiFFI = runApiFFIAC

instance ( Alg sig m
         , HasForeignDef api
         , HasForeign sig m
         , Has (State PState) sig m
         , Has Trace sig m
         , MonadIO m)
      => Algebra (Api api c :+: sig) (ApiFFIAC api c m) where
  alg hdl sig ctx = ApiFFIAC $ case sig of
    L (MkCall k call attrs) -> do
      s <- get @PState
      let args = evalDirects s attrs
      case apiArgsAreValid call args of
        Just err -> throwError (ApiError (showApiFromPat call (args2Pat args)) err)
        Nothing  -> do
          trace $ showApiFromPat call (args2Pat args)
          r <- evalForeign call args
          modify @PState (record k r)
          return (ctx $> ())
    R other -> alg (runApiFFIAC . hdl) other ctx

-- | Trace

newtype ApiTraceAC (api :: ApiDefinition) (c :: Type -> Constraint) m a = ApiTraceAC { runApiTraceAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiTrace :: forall api c m a . Monad m => ApiTraceAC api c m a -> m a
runApiTrace = runApiTraceAC

instance ( Algebra sig m
         , HasForeignDef api
         , Has (State PState) sig m
         , Has (Writer (ApiTrace api c)) sig m)
      => Algebra (Api api c :+: sig) (ApiTraceAC api c m) where
  alg hdl sig ctx = ApiTraceAC $ case sig of
    L (MkCall k call args) -> do
      tell (traceCall @api @c k call args)
      return (ctx $> ())
    R other -> alg (runApiTraceAC . hdl) other ctx
