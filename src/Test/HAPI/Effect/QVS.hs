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
{-# LANGUAGE TemplateHaskell #-}

{-
Quantified Value Generation Effect
-}

module Test.HAPI.Effect.QVS where
import Control.Algebra (Algebra (alg), type (:+:) (L, R), Has, send)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Test.HAPI.Effect.Gen (GenAC(runGenAC), GenA (LiftGenA), liftGenA, oneof, oneof')
import Test.QuickCheck (Arbitrary(arbitrary), chooseInt, chooseEnum)
import Data.Kind (Constraint, Type)
import Data.Functor (($>))
import Control.Carrier.State.Church (StateC, get)
import Control.Effect.State ( State, gets )
import Control.Effect.Sum (Member, Members)
import Test.QuickCheck.Gen (Gen)
import Test.QuickCheck.GenT (MonadGen (liftGen))
import Test.HAPI.PState (PKey, PState, PStateSupports (lookUp))
import Test.HAPI.Common (Fuzzable)
import Data.Maybe (fromJust)
import Data.HList (HList (HNil), HMap,type  (:~:) (Refl))
import Data.SOP ( Proxy(Proxy), NP(..), All, hcmap )
import Test.HAPI.Args (Args, pattern (::*), Attribute (..), validate, DirectAttribute (..), ExogenousAttribute (..), Attributes, evalDirect, DirAttributes, simplifyDirect)
import Data.SOP.Dict (mapAll)
import Data.Serialize (Serialize)
import Test.HAPI.Effect.Orchestration (Orchestration, nextInstruction, OrchestrationError)
import Test.HAPI.Effect.Orchestration.Labels (QVSSupply)
import Data.Type.Equality (castWith, TestEquality (testEquality), apply)
import Type.Reflection ( TypeRep, typeOf, Typeable, typeRep )
import Test.HAPI.Constraint (type (:>>>:), castC)
import Data.Constraint ((\\), mapDict, Dict (..))
import Control.Effect.Error (Error, liftEither, throwError)
import Control.Carrier.Error.Either (runError)
import Data.Either.Combinators (mapLeft)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR))
import Test.HAPI.Serialize (HSerialize)
import qualified Test.HAPI.Serialize as HS
import qualified Data.Serialize as S


-- Quantified Value Supplier
data QVS (c :: Type -> Constraint) (m :: Type -> Type) a where
  QDirect    :: (Typeable a, c a) => DirectAttribute c a    -> QVS c m a
  QExogenous :: (Fuzzable a, c a) => ExogenousAttribute c a -> QVS c m a

data QVSError = QVSError { causedAttribute :: String, errorMessage :: String }
  deriving Show

mkQVS :: forall c a m. Typeable c => Attribute c a -> QVS c m a
mkQVS (Direct    d) = QDirect d
mkQVS (Exogenous e) = QExogenous e

-- | Convert attribute to QVS
attributes2QVSs :: forall c p m. Typeable c => Attributes c p -> NP (QVS c m) p
attributes2QVSs Nil = Nil
attributes2QVSs (a :* as) = mkQVS a :* attributes2QVSs as

-- | Generate values in HList
qvs2m :: (Has (QVS c) sig m) => NP (QVS c m) p -> m (Args p)
qvs2m Nil = return Nil
qvs2m (qvs :* q) = do
  a <- send qvs
  s <- qvs2m q
  return (a ::* s)

qvs2Direct :: (Has (QVS c :+: State PState) sig m) => QVS c m a -> m (DirectAttribute c a)
qvs2Direct qvs = case qvs of
    QDirect d     -> gets (`simplifyDirect` d)
    QExogenous {} -> Value <$> send qvs

qvs2Directs :: (Has (QVS c :+: State PState) sig m) => NP (QVS c m) p -> m (DirAttributes c p)
qvs2Directs Nil = return Nil
qvs2Directs (qvs :* q) = do
  d <- qvs2Direct qvs
  s <- qvs2Directs q
  return (d :* s)


newtype QVSFuzzArbitraryAC (c :: Type -> Constraint) m a = QVSFuzzArbitraryAC { runQVSFuzzArbitraryAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO)

instance (Algebra sig m, Members (State PState :+: GenA) sig, c :>>>: Arbitrary) => Algebra (QVS c :+: sig) (QVSFuzzArbitraryAC c m) where
  alg hdl sig ctx = QVSFuzzArbitraryAC $ case sig of
    L qvs   -> resolveQVS qvs
    R other -> alg (runQVSFuzzArbitraryAC . hdl) other ctx
    where
      resolveQVS (qvs :: QVS c n a) = case qvs of
        QDirect d -> do
          s <- get @PState
          return (ctx $> evalDirect s d)
        QExogenous Anything     -> do
          v <- liftGenA (arbitrary \\ castC @Arbitrary (Dict @(c a)))
          return (ctx $> v)
        QExogenous (IntRange l r) -> do
          v <- liftGenA (chooseInt (l, r))
          return (ctx $> v)
        QExogenous (Range    l r) -> do
          v <- liftGenA (chooseEnum (l, r))
          return (ctx $> v)
        -- Exogenous AnyOf xs     -> do
          -- a <- oneof' (return <$> xs)
          -- resolveQVS (QVS a)

-- newtype QVSFromStdinAC (c :: Type -> Constraint) m a = QVSFromStdinAC { runQVSFromStdinAC :: m a }
--   deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

-- instance ( Algebra sig m
--          , Has (Error QVSError)          sig m
--          , Has (State PState)            sig m
--          , MonadIO m
--          , c :>>>: Read)
--       => Algebra (QVS c :+: sig) (QVSFromStdinAC c m) where
--   alg hdl sig ctx = QVSFromStdinAC $ case sig of
--     L qvs -> do
--       input <- case attr of
--         Direct (Get x)                          -> do
--           v <- gets @PState (lookUp x)
--           case v of
--             Nothing -> throwError (QVSError (show attr) "Variable not in scope!")
--             Just a  -> return a
--         Direct (Value v) -> return v
--         Exogenous (a :: ExogenousAttribute c a) -> liftIO (putStrLn "Please provide input: " >> readAndValidate attr) \\ castC @Read (Dict @(c a))
--       return (ctx $> input)
--     R other -> alg (runQVSFromStdinAC . hdl) other ctx
--     where
--       readAndValidate attr = do
--         a <- readLn
--         if validate attr a
--           then return a
--           else fail "Not in range"

newtype QVSFromOrchestrationAC (c0 :: Type -> Constraint) (c :: Type -> Constraint) m a = QVSFromOrchestrationAC { runQVSFromOrchestrationAC :: m a }
  deriving (Functor, Applicative, Monad, MonadFail)

instance ( Has (Orchestration QVSSupply) sig m
         , Has (State PState)            sig m
         , Has (Error QVSError)          sig m
         , c :>>>: Serialize)
      => Algebra (QVS c :+: sig) (QVSFromOrchestrationAC Serialize c m) where
  alg hdl sig ctx = QVSFromOrchestrationAC $ case sig of
    L qvs   -> resolveQVS qvs
    R other -> alg (runQVSFromOrchestrationAC . hdl) other ctx
    where
      resolveQVS (qvs :: QVS c n a) = case qvs of
        QDirect d -> do
          s <- get @PState
          return (ctx $> evalDirect s d)
        QExogenous a@Anything     -> do
          v <- next (show a) \\ castC @Serialize (Dict @(c a))
          return (ctx $> v)
        QExogenous a@(IntRange l r) -> do
          v <- next (show a)
          return (ctx $> sampleRange l r v)
        QExogenous a@(Range    l r) -> do
          v <- next (show a)
          return (ctx $> sampleRange l r v)
        where
          next attr = do
            x <- nextInstruction @QVSSupply S.get
            case x of
              Nothing -> throwError (QVSError attr "QVS supplier exhausted")
              Just  a -> return a

          sampleRange l r v = toEnum $ l' + (v `mod` (r' - l' + 1))
            where
              l' = fromEnum l
              r' = fromEnum r


instance ( Has (Orchestration QVSSupply) sig m
         , Has (State PState)            sig m
         , Has (Error QVSError)          sig m
         , c :>>>: HSerialize)
      => Algebra (QVS c :+: sig) (QVSFromOrchestrationAC HSerialize c m) where
  alg hdl sig ctx = QVSFromOrchestrationAC $ case sig of
    L qvs   -> resolveQVS qvs
    R other -> alg (runQVSFromOrchestrationAC . hdl) other ctx
    where
      resolveQVS (qvs :: QVS c n a) = case qvs of
        QDirect d -> do
          s <- get @PState
          return (ctx $> evalDirect s d)
        QExogenous a@Anything     -> do
          v <- next (show a) \\ castC @HSerialize (Dict @(c a))
          return (ctx $> v)
        QExogenous a@(IntRange l r) -> do
          v <- next (show a)
          return (ctx $> sampleRange l r v)
        QExogenous a@(Range    l r) -> do
          v <- next (show a)
          return (ctx $> sampleRange l r v)
        where
          next attr = do
            x <- nextInstruction @QVSSupply HS.hget
            case x of
              Nothing -> throwError (QVSError attr "QVS supplier exhausted")
              Just  a -> return a

          sampleRange l r v = toEnum $ l' + (v `mod` (r' - l' + 1))
            where
              l' = fromEnum l
              r' = fromEnum r
