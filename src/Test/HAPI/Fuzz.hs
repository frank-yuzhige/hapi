{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Test.HAPI.Fuzz where
import Control.Algebra (Algebra (alg), type (:+:) (L, R), Has, send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Test.HAPI.GenT (GenAC(runGenAC), GenA (LiftGenA))
import Test.QuickCheck (Arbitrary(arbitrary))
import Data.Kind (Constraint, Type)
import Data.Functor (($>))

data FuzzA (technique :: * -> Constraint) (m :: * -> *) a where
  AnyA :: (technique a) => FuzzA technique m a

-- anyA :: (Has (FuzzA technique) sig m) => m a
-- anyA = send AnyA

newtype FuzzQCGenAC m a = FuzzQCGenAC { runFuzzQCGenAC :: GenAC m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

instance (Algebra sig m) => Algebra (FuzzA Arbitrary :+: sig) (FuzzQCGenAC m) where
  alg hdl sig ctx = case sig of
    L fuzz -> case fuzz of
      AnyA -> FuzzQCGenAC $ alg (runFuzzQCGenAC . hdl) (L (LiftGenA arbitrary)) ctx
    R other -> alg (FuzzQCGenAC . runFuzzQCGenAC . hdl) (R other) ctx

newtype FuzzIOReadAC m a = FuzzIOReadAC { runFuzzIOReadAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m) => Algebra (FuzzA Read :+: sig) (FuzzIOReadAC m) where
  alg hdl sig ctx = case sig of
    L fuzz -> case fuzz of
      AnyA -> do
        input <- liftIO readLn
        return (ctx $> input)
    R other -> FuzzIOReadAC $ alg (runFuzzIOReadAC . hdl) other ctx
