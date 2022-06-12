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

module Test.HAPI.Effect.Gen where
import Test.QuickCheck (Gen, Arbitrary (arbitrary), resize, variant)
import System.Random (Random)
import Test.QuickCheck.GenT (GenT (GenT), MonadGen, runGenT)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Algebra ( Algebra, type (:+:)(L, R), send, Has, run )
import Control.Effect.Labelled (Algebra(alg))
import Control.Monad.Trans.Class (MonadTrans (lift))
import Data.Functor (($>))
import Test.QuickCheck.Gen (generate)
import Control.Monad (join)
import qualified Data.List.NonEmpty as NE
import qualified Test.QuickCheck.GenT as GenT


data GenA (m :: * -> *) a where
  -- | Lift a Gen to effect
  LiftGenA :: Gen a -> GenA m a
  -- -- | Modifies a generator using an integer seed
  -- VariantA :: Integral k => k -> m a -> GenA m a
  -- -- | Used to construct generators that depend on the size parameter.
  -- SizedA   :: (Int -> m a) -> GenA m a
  -- -- | Overrides the size parameter. Returns a generator which uses the given size instead of the runtime-size parameter.
  -- ResizeA  :: Int -> m a -> GenA m a
  -- -- | Generates a random element in the given inclusive range.
  -- ChooseA  :: Random a => (a, a) -> GenA m a

liftGenA :: (Has GenA sig m) => Gen a -> m a
liftGenA = send . LiftGenA

-- variantA :: (Has GenA sig m, Integral k) => k -> m a -> m a
-- variantA = (send .) . VariantA

-- sizedA :: (Has GenA sig m) => (Int -> m a) -> m a
-- sizedA = send . SizedA

-- resizeA :: (Has GenA sig m) => Int -> m a -> m a
-- resizeA = (send .) . ResizeA

-- chooseA :: (Has GenA sig m, Random a) => (a, a) -> m a
-- chooseA = send . ChooseA

-- | Interpretation using GenT
newtype GenAC m a = GenAC { runGenAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, MonadGen)

runGenIO :: MonadIO m => GenAC m a -> m a
runGenIO = runGenAC

instance (Algebra sig m, MonadIO m) => Algebra (GenA :+: sig) (GenAC m) where
  alg hdl sig ctx = case sig of
    L genA -> case genA of
      LiftGenA qcGen -> do
        g <- liftIO $ generate qcGen
        return $ ctx $> g
      -- VariantA k g -> do
      --   g <- liftIO $ variant k $ hdl (ctx $> g)
      --   _
      -- SizedA f ->
      --   GenT.sized $ \i -> hdl (ctx $> f i)
      -- ResizeA k g ->
      --   GenT.resize k $ hdl (ctx $> g)
      -- ChooseA r -> do
      --   c <- GenT.choose r
      --   return (ctx $> c)
    R other -> alg (GenAC . runGenAC . hdl) (R other) ctx

-- | Lifted Operations

anyVal :: forall a m sig. (Has GenA sig m, Arbitrary a) => m a
anyVal = liftGenA arbitrary

suchThat :: (Has GenA sig m, Arbitrary a) => m a -> (a -> Bool) -> m a
suchThat gen p = do
  a <- gen
  if p a then return a else suchThat gen p

-- oneof :: (Has GenA sig m) => NE.NonEmpty (m a) -> m a
-- oneof xs = chooseA (0, length xs - 1) >>= (xs NE.!!)
-- {-# INLINE oneof #-}

-- oneof' :: (Has GenA sig m) => [m a] -> m a
-- oneof' [] = error "oneof' used with empty list!"
-- oneof' xs = oneof (NE.fromList xs)

-- frequency :: (Has GenA sig m) => NE.NonEmpty (Int, m a) -> m a
-- frequency freqs = chooseA (0, total) >>= (`pick` NE.toList freqs)
--   where
--     total = sum $ fmap fst freqs
--     pick n ((a, m) : xs)
--       | n <= a    = m
--       | otherwise = pick (n - a) xs
--     pick _ _ = error "pick on empty list"

-- frequency' :: (Has GenA sig m) => [(Int, m a)] -> m a
-- frequency' [] = error "frequency' used with empty list!"
-- frequency' xs = frequency (NE.fromList xs)

-- anyof' :: (Has GenA sig m) => [a] -> m a
-- anyof' [] = error "anyof' used with empty list!"
-- anyof' xs = (xs !!) <$> chooseA (0, length xs - 1)
