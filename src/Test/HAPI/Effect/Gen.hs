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

liftGenA :: (Has GenA sig m) => Gen a -> m a
liftGenA = send . LiftGenA


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
    R other -> alg (GenAC . runGenAC . hdl) (R other) ctx

-- | Lifted Operations

anyVal :: forall a m sig. (Has GenA sig m, Arbitrary a) => m a
anyVal = liftGenA arbitrary

suchThat :: (Has GenA sig m, Arbitrary a) => m a -> (a -> Bool) -> m a
suchThat gen p = do
  a <- gen
  if p a then return a else suchThat gen p
