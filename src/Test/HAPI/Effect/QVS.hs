{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-
Quantified Value Generation Effect
-}

module Test.HAPI.Effect.QVS where
import Control.Algebra (Algebra (alg), type (:+:) (L, R), Has, send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Test.HAPI.Effect.Gen (GenAC(runGenAC), GenA (LiftGenA), liftGenA)
import Test.QuickCheck (Arbitrary(arbitrary), chooseInt, chooseEnum)
import Data.Kind (Constraint, Type)
import Data.Functor (($>))
import Data.Data (Proxy)
import Control.Carrier.State.Church (StateC, get)
import Control.Effect.State ( State, gets )
import Control.Effect.Sum (Member, Members)
import Test.HAPI.DataType (TypeSpec, GetSpecCons, TyMember, WFTypeSpec, GetSpecTypes, WFTypeSpec_, TyIn)
import Test.QuickCheck.Gen (Gen)
import Test.QuickCheck.GenT (MonadGen (liftGen))
import Test.HAPI.PState (PKey, PState, PStateSupports (lookUp))
import Test.HAPI.Common (Fuzzable)
import Data.Maybe (fromJust)
import Data.HList (HList (HNil), HMap)
import Data.SOP
import Test.HAPI.Args (Args, pattern (::*))
import Data.SOP.Dict (mapAll, Dict (Dict))

data Attribute a where
  Anything :: (Fuzzable a) => Attribute a
  IntRange :: Int -> Int -> Attribute Int
  Range    :: (Fuzzable a, Ord a, Enum a)
           => a -> a -> Attribute a
  Get      :: (Fuzzable a) => PKey a -> Attribute a


-- Quantified Value Supplier
data QVS (c :: Type -> Constraint) (m :: Type -> Type) a where
  QVS :: (c a) => Attribute a -> QVS c m a


-- https://hackage.haskell.org/package/sop-core-0.5.0.2/docs/Data-SOP-NP.html
type LiftArgs (f :: Type -> Type) (p :: [Type]) = NP f p


-- | Convert attribute to QVS
attributes2QVSs :: forall c p m. (All c p) => NP Attribute p -> NP (QVS c m) p
attributes2QVSs = hcmap (Proxy @c) QVS

-- | Generate values in HList
qvs2m :: (Has (QVS c) sig m) => LiftArgs (QVS c m) p -> m (Args p)
qvs2m Nil = return Nil
qvs2m (qvs :* q) = do
  a <- send qvs
  s <- qvs2m q
  return (a ::* s)

newtype QVSFuzzArbitraryCA s m a = QVFuzzArbitraryCA { runQVSFuzzArbitraryCA :: m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

instance (Algebra sig m, Members (State PState :+: GenA) sig) => Algebra (QVS Arbitrary :+: sig) (QVSFuzzArbitraryCA spec m) where
  alg hdl sig ctx = QVFuzzArbitraryCA $ case sig of
    L (QVS attr) -> case attr of
      Anything          -> do
        a <- liftGenA arbitrary
        return (ctx $> a)
      IntRange l r -> do
        a <- liftGenA (chooseInt (l, r))
        return (ctx $> a)
      Range    l r -> do
        a <- liftGenA (chooseEnum (l, r))
        return (ctx $> a)
      Get k        -> do
        a <- gets @PState (lookUp k)
        return (ctx $> fromJust a)
    R other -> alg (runQVSFuzzArbitraryCA . hdl) other ctx

newtype QVSFromStdin m a = QVSFromStdin { runQVSFromStdin :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m) => Algebra (QVS Read :+: sig) (QVSFromStdin m) where
  alg hdl sig ctx = case sig of
    L qvs -> do
      liftIO (putStrLn "Please provide input: ")
      input <- liftIO $ case qvs of QVS attr -> readAndValidate attr
      return (ctx $> input)
    R other -> QVSFromStdin $ alg (runQVSFromStdin . hdl) other ctx
    where
      readAndValidate attr = do
        a <- readLn
        if validate attr a
          then return a
          else fail "Not in range"


-- | Check if the provided value satisfies the
validate :: Attribute a -> a -> Bool
validate attr a = case attr of
  IntRange l r -> l <= a && a <= r
  Range    l r -> l <= a && a <= r
  _            -> True
