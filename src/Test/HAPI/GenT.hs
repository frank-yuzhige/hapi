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
import qualified Data.List.NonEmpty as NE


data GenA (m :: * -> *) a where
  LiftGenA :: Gen a -> GenA m a
  VariantA :: Integral k => k -> GenA m a -> GenA m a
  SizedA   :: (Int -> GenA m a) -> GenA m a
  ResizeA  :: Int -> GenA m a -> GenA m a
  ChooseA  :: Random a => (a, a) -> GenA m a

liftGenA :: Has GenA sig m => Gen a -> m a
liftGenA = send . LiftGenA

chooseA :: (Has GenA sig m, Random a) => (a, a) -> m a
chooseA = send. ChooseA

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
      VariantA k g ->
        variant k $ alg (GenAC . runGenAC . hdl) (L g) ctx
      SizedA f ->
        sized $ \i -> alg (GenAC . runGenAC . hdl) (L (f i)) ctx
      ResizeA k g ->
        resize k $ alg (GenAC . runGenAC . hdl) (L g) ctx
      ChooseA r -> do
        c <- choose r
        return (ctx $> c)
    R other -> alg (GenAC . runGenAC . hdl) (R other) ctx

-- | Lifted Operations

anyVal :: forall a m sig. (Has GenA sig m, Arbitrary a) => m a
anyVal = liftGenA arbitrary

suchThat :: (Has GenA sig m, Arbitrary a) => m a -> (a -> Bool) -> m a
suchThat gen p = do
  a <- gen
  if p a then return a else suchThat gen p

oneof :: (Has GenA sig m) => NE.NonEmpty (m a) -> m a
oneof xs = chooseA (0, length xs - 1) >>= (xs NE.!!)
{-# INLINE oneof #-}

oneof' :: (Has GenA sig m) => [m a] -> m a
oneof' [] = error "oneof' used with empty list!"
oneof' xs = oneof (NE.fromList xs)

frequency :: (Has GenA sig m) => NE.NonEmpty (Int, m a) -> m a
frequency freqs = chooseA (0, total) >>= (`pick` NE.toList freqs)
  where
    total = sum $ fmap fst freqs
    pick n ((a, m) : xs)
      | n <= a    = m
      | otherwise = pick (n - a) xs
    pick _ _ = error "pick on empty list"

frequency' :: (Has GenA sig m) => [(Int, m a)] -> m a
frequency' [] = error "frequency' used with empty list!"
frequency' xs = frequency (NE.fromList xs)

anyOf' :: (Has GenA sig m) => [a] -> m a
anyOf' [] = error "anyOf' used with empty list!"
anyOf' xs = (xs !!) <$> chooseA (0, length xs - 1)
