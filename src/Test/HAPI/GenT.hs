{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module Test.HAPI.GenT where
import Test.QuickCheck (Gen, Arbitrary (arbitrary))
import System.Random (Random)
import Test.QuickCheck.GenT (GenT (GenT), MonadGen (liftGen, variant, sized, resize, choose), runGenT)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Algebra ( Algebra, type (:+:)(L, R), send, Has, run )
import Control.Effect.Labelled (Algebra(alg))
import Control.Monad.Trans.Class (MonadTrans (lift))
import Data.Functor (($>))
import Test.QuickCheck.Gen (generate)
import Control.Monad (join)


data GenA (m :: * -> *) a where
  LiftGenA :: Gen a -> GenA m a
  VariantA :: Integral k => k -> m a -> GenA m a
  SizedA   :: (Int -> m a) -> GenA m a
  ResizeA  :: Int -> m a -> GenA m a
  ChooseA  :: Random a => (a, a) -> GenA m a

liftGenA :: Has GenA sig m => Gen a -> m a
liftGenA = send . LiftGenA

arbitraryA :: forall a m sig. (Has GenA sig m, Arbitrary a) => m a
arbitraryA = liftGenA arbitrary

newtype GenAC m a = GenAC { runGenAC :: GenT m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, MonadGen, MonadTrans)

genIO :: MonadIO m => GenT m a -> m a
genIO = join . liftIO . generate . runGenT

instance (Algebra sig m) => Algebra (GenA :+: sig) (GenAC m) where
  alg hdl sig ctx = case sig of
    L genA   -> case genA of
      LiftGenA qcGen -> do
        g <- liftGen qcGen
        return $ ctx $> g
      VariantA k g -> variant k (hdl (ctx $> g))
      SizedA f -> undefined  -- TODO How to implement this???
      ResizeA k g -> resize k (hdl (ctx $> g))
      ChooseA r -> do
        c <- choose r
        return (ctx $> c)
    R other -> alg (GenAC . runGenAC . hdl) (R other) ctx
