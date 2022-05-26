{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Test.HAPI.Effect.Property where

import Control.Algebra ( send, Algebra(..), Has, type (:+:)(..) )
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Trans.Class (MonadTrans)
import Data.Functor (($>))
import Control.Carrier.Error.Church( Catch, ErrorC, throwError )
import Control.Effect.Error (Error)
import Test.QuickCheck (Arbitrary)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.Args (DirectAttribute (..), evalDirect)
import Test.HAPI.PState (PState)
import Control.Effect.State (State, get)
import Control.Effect.Writer (Writer, tell)
import Test.HAPI.Api (ApiDefinition)
import Data.Constraint (Constraint)
import Data.Kind (Type)
import Test.HAPI.ApiTrace.Core ( ApiTrace, traceAssert )

type PropertyType = (* -> *) -> * -> *

data PropertyError where
  AssertError   :: DirectAttribute Bool -> PropertyError
  FailedError   :: PropertyError

instance Show PropertyError where
  show (AssertError b)     = "Error: " <> show b <> " is false"
  show FailedError         = "Error: Expect the property not to reach this point"

data PropertyA (m :: * -> *) a where
  AssertA   :: DirectAttribute Bool -> PropertyA m ()
  FailedA   :: PropertyA m ()

class Property (prop :: PropertyType) err pstate | prop -> err pstate where
  evalProperty :: pstate -> prop m a -> Either err a

instance Property PropertyA PropertyError PState where
  evalProperty _ FailedA     = Left FailedError
  evalProperty s (AssertA d)
    | evalDirect s d = Right ()
    | otherwise      = Left (AssertError d)


newtype PropertyAC (prop :: PropertyType) err m a = PropertyAC { runPropertyAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runProperty :: forall prop err sig m a. PropertyAC prop err m a -> m a
runProperty = runPropertyAC

instance ( Algebra sig m
         , Has (Error err) sig m
         , Has (State PState) sig m
         , Property prop err PState) => Algebra (prop :+: sig) (PropertyAC prop err m) where
  alg hdl sig ctx = PropertyAC $ case sig of
    L prop  -> do
      s <- get @PState
      case evalProperty s prop of
        Left  err -> throwError err
        Right a   -> return (ctx $> a)
    R other -> alg (runPropertyAC . hdl) other ctx

newtype PropertyTraceAC err (api :: ApiDefinition) (c :: Type -> Constraint) m a = PropertyTraceAC { runPropertyTraceAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runPropertyTrace :: forall err api c sig m a. PropertyTraceAC err api c m a -> m a
runPropertyTrace = runPropertyTraceAC

instance ( Algebra sig m
         , Has (Error err) sig m
         , Has (State PState) sig m
         , Has (Writer (ApiTrace api c)) sig m
         , Property PropertyA err PState
         , c Bool) => Algebra (PropertyA :+: sig) (PropertyTraceAC err api c m) where
  alg hdl sig ctx = PropertyTraceAC $ case sig of
    L (AssertA a)  -> do
      tell (traceAssert @api @c a)
      return (ctx $> ())
    L FailedA      -> do
      tell (traceAssert @api @c (Value False))
      return (ctx $> ())
    R other -> alg (runPropertyTraceAC . hdl) other ctx
