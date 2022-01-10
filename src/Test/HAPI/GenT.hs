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
  VariantA :: Integral k => k -> GenA m a -> GenA m a
  SizedA   :: (Int -> GenA m a) -> GenA m a
  ResizeA  :: Int -> GenA m a -> GenA m a
  ChooseA  :: Random a => (a, a) -> GenA m a

changeBasis :: GenA m a -> GenA n a
changeBasis (LiftGenA gen) = LiftGenA gen
changeBasis (VariantA k ma) = VariantA k (changeBasis ma)
changeBasis (SizedA f) = SizedA $ \i -> changeBasis (f i)
changeBasis (ResizeA n ma) = ResizeA n (changeBasis ma)
changeBasis (ChooseA r) = ChooseA r

liftGenA :: Has GenA sig m => Gen a -> m a
liftGenA = send . LiftGenA

arbitraryA :: forall a m sig. (Has GenA sig m, Arbitrary a) => m a
arbitraryA = liftGenA arbitrary

suchThat :: (Has GenA sig m, Arbitrary a) => m a -> (a -> Bool) -> m a
suchThat gen p = do
  a <- gen
  if p a then return a else suchThat gen p

newtype GenAC m a = GenAC { runGenAC :: GenT m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, MonadGen, MonadTrans)

runGenIO :: MonadIO m => GenAC m a -> m a
runGenIO = join . liftIO . generate . runGenT . runGenAC

instance (Algebra sig m) => Algebra (GenA :+: sig) (GenAC m) where
  alg hdl sig ctx = case sig of
    L genA   -> case genA of
      LiftGenA qcGen -> do
        g <- liftGen qcGen
        return $ ctx $> g
      VariantA k g -> variant k $ alg (GenAC . runGenAC . hdl) (L g) ctx
      SizedA f -> sized $ \i -> alg (GenAC . runGenAC . hdl) (L (f i)) ctx
      ResizeA k g -> resize k $ alg (GenAC . runGenAC . hdl) (L g) ctx
      ChooseA r -> do
        c <- choose r
        return (ctx $> c)
    R other -> alg (GenAC . runGenAC . hdl) (R other) ctx
