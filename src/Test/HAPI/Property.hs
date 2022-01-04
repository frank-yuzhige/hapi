{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module Test.HAPI.Property where

import Control.Algebra ( send, Algebra(..), Has, type (:+:)(..) )
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans)
import Data.Functor (($>))
import Control.Carrier.Error.Church( Catch, ErrorC, throwError, throwError )
import Control.Carrier.Cull.Church (MonadPlus)
import Control.Effect.Error (Error)
import Test.QuickCheck (Arbitrary)

type PropertyType = (* -> *) -> * -> *

data PropertyError where
  MismatchError :: Show a => a -> a -> PropertyError

instance Show PropertyError where
  show (MismatchError a b) = "Error: " <> show a <> " != " <> show b

data PropertyA (m :: * -> *) a where
  ShouldBeA  :: (Eq a, Show a) => a -> a -> PropertyA m ()

shouldBe :: (Eq a, Show a, Has PropertyA sig m) => a -> a -> m ()
shouldBe a b = send $ ShouldBeA a b

newtype PropertyAC (prop :: PropertyType) err m a = PropertyAC { runPropertyTypeAC :: ErrorC err m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail, MonadTrans)

runProperty :: forall prop err sig m a. PropertyAC prop err m a -> ErrorC err m a
runProperty = runPropertyTypeAC

class Property (prop :: PropertyType) err | prop -> err where
  evalProperty :: prop m a -> Either err a

instance Property PropertyA PropertyError where
  evalProperty (ShouldBeA a b) = if a == b then Right () else Left (MismatchError a b)

instance (Algebra sig m, Property prop err) => Algebra (prop :+: sig) (PropertyAC prop err m) where
  alg hdl sig ctx = PropertyAC $ case sig of
    L prop  -> do
      case evalProperty prop of
        Left  err -> throwError err
        Right a   -> return (ctx $> a)
    R other -> alg (runPropertyTypeAC . hdl) (R other) ctx
