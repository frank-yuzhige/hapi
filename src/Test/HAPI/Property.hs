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
module Test.HAPI.Property where

import Control.Algebra ( send, Algebra(..), Has, type (:+:)(..) )
import Control.Monad.IO.Class (MonadIO)
import Data.Functor (($>))
import Control.Carrier.Throw.Either (ThrowC, runThrow, throwError)
import Control.Effect.Throw (Throw)

type PropertyType = (* -> *) -> * -> *

data PropertyError where
  MismatchError :: Show a => a -> a -> PropertyError

deriving instance Show PropertyError

data PropertyA (m :: * -> *) a where
  ShouldBeA :: (Eq a, Show a) => a -> a -> PropertyA m Bool

shouldBe :: (Eq a, Show a, Has PropertyA sig m) => a -> a -> m Bool
shouldBe a b = send $ ShouldBeA a b

newtype PropertyAC (prop :: PropertyType) err m a = PropertyAC { runPropertyTypeAC :: ThrowC err m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runProperty :: PropertyAC prop err m a -> m (Either err a)
runProperty = runThrow . runPropertyTypeAC

class Property (prop :: PropertyType) err | prop -> err where
  evalProperty :: prop m a -> Either a err

instance Property PropertyA PropertyError where
  evalProperty (ShouldBeA a b) = if a == b then Left True else Right (MismatchError a b)

instance (Algebra sig m, Has (Throw err) sig m, Property prop err) => Algebra (prop :+: sig) (PropertyAC prop err m) where
  alg hdl sig ctx = PropertyAC $ case sig of
    L prop  -> do
      case evalProperty prop of
        Left  a   -> return (ctx $> a)
        Right err -> throwError err
    R other -> alg (runPropertyTypeAC . hdl) (R other) ctx
