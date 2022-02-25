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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

{-
Quantified Value Generation Effect
-}

module Test.HAPI.QVS where
import Control.Algebra (Algebra (alg), type (:+:) (L, R), Has, send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Test.HAPI.GenT (GenAC(runGenAC), GenA (LiftGenA), liftGenA)
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
import Data.HList (HList (HNil))
import Test.HAPI.Args (pattern (:::))

data Attribute a where
  Anything :: (Fuzzable a) => Attribute a
  IntRange :: Int -> Int -> Attribute Int
  Range    :: (Fuzzable a, Ord a, Enum a)
           => a -> a -> Attribute a
  Get      :: (Fuzzable a) => PKey a -> Attribute a


-- Quantified Value Supplier
data QVS (c :: Type -> Constraint) (m :: Type -> Type) a where
  QVS :: (c a) => Attribute a -> QVS c m a


type family ArgsAttributes s (p :: [Type]) :: [Type] where
  ArgsAttributes s '[] = '[]
  ArgsAttributes s (x : xs) = Attribute x : ArgsAttributes s xs

class Attributes2QVSs attr qvs | qvs -> attr where
  attributes2QVSs :: HList attr -> HList qvs

instance Attributes2QVSs '[] '[] where
  attributes2QVSs _ = HNil

instance (Attributes2QVSs as qs, c a) => Attributes2QVSs (Attribute a : as) (QVS c m a : qs) where
  attributes2QVSs (a ::: as) = QVS a ::: attributes2QVSs as


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

newtype QVSFromStdin s m a = QVSFromStdin { runQVSFromStdin :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m) => Algebra (QVS Read :+: sig) (QVSFromStdin spec m) where
  alg hdl sig ctx = case sig of
    L qvs -> do
      liftIO (putStrLn "Please provide input: ")
      input <- liftIO $ case qvs of QVS {} -> readAndValidate qvs
      return (ctx $> input)
    R other -> QVSFromStdin $ alg (runQVSFromStdin . hdl) other ctx
    where
      readAndValidate qvs = do
        a <- readLn
        if validate qvs a
          then return a
          else fail "Not in range"


validate :: QVS c m a -> a -> Bool
validate (QVS attr) a = case attr of
  IntRange l r -> l <= a && a <= r
  Range    l r -> l <= a && a <= r
  _            -> True
