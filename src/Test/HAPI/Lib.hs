{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module Test.HAPI.Lib where

import Control.Algebra ( Has, type (:+:), send, Algebra )
import Test.HAPI.Api ( HaskellIOCall(..), HasHaskellDef(..), HasForeignDef (evalForeign), ApiDefinition )
import Test.HAPI.Effect.Api (runApi, runApiIO, runApiFFI, ApiFFIAC (ApiFFIAC), Api, mkCall)
import Test.HAPI.Effect.Property (PropertyA, runProperty, shouldBe, PropertyError, PropertyAC (..), failed, shouldReturn)
import Text.Read (readMaybe)
import Control.Carrier.Error.Church (Catch, Error, Throw, catchError, runError, ErrorC)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad (void, replicateM, forM, forM_)
import Test.HAPI.Effect.Gen (GenA, liftGenA, GenAC (runGenAC), anyVal, runGenIO, suchThat, chooseA)
import Test.QuickCheck.GenT (MonadGen(liftGen), runGenT)
import Test.QuickCheck (Arbitrary(arbitrary), generate)
import Test.HAPI.FFI (add, sub, mul, neg, str, Stack, createStack, pushStack, popStack, peekStack, getStackSize)
import Control.Effect.Labelled (Labelled(Labelled))
import Foreign.C (peekCString)
import Test.HAPI.Effect.QVS (QVS (QVS), QVSFuzzArbitraryCA (runQVSFuzzArbitraryCA), QVSFromStdin (runQVSFromStdin), Attribute (IntRange))
import Test.QuickCheck.Random (QCGen(QCGen))
import Data.Data (Proxy (Proxy))
import Foreign (Ptr)
import Test.HAPI.Constraint (type (:>>>:))
import Test.HAPI.DataType (BasicSpec, WFTypeSpec, type (:&:))
import Data.HList (HList(HNil, HCons))
import Test.HAPI.Args (args, mkArgs, noArgs)


data ArithApiA :: ApiDefinition where
  AddA :: ArithApiA '[Int, Int] Int
  SubA :: ArithApiA '[Int, Int] Int
  MulA :: ArithApiA '[Int, Int] Int
  NegA :: ArithApiA '[Int, Int] Int

data ShowApiA :: ApiDefinition where
  StrA :: ShowApiA '[Int] String

data StackApiA :: ApiDefinition where
  CreateA :: StackApiA '[]               (Ptr Stack)
  PushA   :: StackApiA '[Ptr Stack, Int] ()
  PopA    :: StackApiA '[Ptr Stack ]     ()
  PeekA   :: StackApiA '[Ptr Stack ]     Int
  SizeA   :: StackApiA '[Ptr Stack ]     Int

deriving instance Show (ArithApiA p a)
deriving instance Show (ShowApiA p a)
deriving instance Show (StackApiA p a)

instance HasHaskellDef ShowApiA where
  evalHaskell StrA [args|a|] = show a

instance HasForeignDef ShowApiA where
  evalForeign StrA [args|a|] = do
    ptr <- str (fromIntegral a)
    liftIO $ peekCString ptr

instance HaskellIOCall ShowApiA where
  readOut StrA = readMaybe
  showArgs = show


instance HasHaskellDef ArithApiA where
  evalHaskell AddA [args|a b|] = a + b
  evalHaskell SubA [args|a b|] = a - b
  evalHaskell MulA [args|a b|] = a * b
  evalHaskell NegA [args|a b|] = -a

instance HasForeignDef ArithApiA where
  evalForeign AddA [args|a b|] = fromIntegral <$> add (fromIntegral a) (fromIntegral b)
  evalForeign SubA [args|a b|] = fromIntegral <$> sub (fromIntegral a) (fromIntegral b)
  evalForeign MulA [args|a b|] = fromIntegral <$> mul (fromIntegral a) (fromIntegral b)
  evalForeign NegA [args|a b|] = fromIntegral <$> neg (fromIntegral a)

instance HaskellIOCall ArithApiA where
  readOut AddA = readMaybe
  readOut SubA = readMaybe
  readOut MulA = readMaybe
  readOut NegA = readMaybe
  showArgs = show

instance HasForeignDef StackApiA where
  evalForeign CreateA [args||]  = createStack
  evalForeign PushA [args|ptr n|] = pushStack ptr (fromIntegral n)
  evalForeign PopA  [args|ptr  |] = popStack  ptr
  evalForeign PeekA [args|ptr  |] = fromIntegral <$> peekStack    ptr
  evalForeign SizeA [args|ptr  |] = fromIntegral <$> getStackSize ptr

-- | Example program, calling arithmetic and show API
show3Plus5Is8 :: Has (Api ArithApiA :+: Api ShowApiA :+: PropertyA) sig m => m ()
show3Plus5Is8 = do
  x <- mkCall AddA $ mkArgs 10 20
  x <- mkCall SubA $ mkArgs (-10005) x
  x <- mkCall StrA $ mkArgs x
  x `shouldBe` "40"

prop :: (MonadIO m, MonadFail m, Algebra sig m) => m ()
prop = runError @PropertyError (fail . show) pure
     . runProperty @PropertyA
     . runApiFFI @ArithApiA
     . runApiIO @ShowApiA
     $ show3Plus5Is8

arb :: forall c sig m. (Has (Api ShowApiA :+: PropertyA :+: QVS c) sig m, WFTypeSpec (BasicSpec c))
    => m ()
arb = do
  a <- send (QVS @c $ IntRange 0 100)
  b <- send (QVS @c $ IntRange 0 100)
  mkCall StrA (mkArgs a) `shouldReturn` show a
  mkCall StrA (mkArgs b) `shouldReturn` show b
  mkCall StrA (mkArgs a) `shouldReturn` show a
  failed

prog1 :: Has (Api ArithApiA :+: PropertyA) sig m => m ()
prog1 = do
  a <- mkCall MulA $ mkArgs 1 2
  b <- mkCall MulA $ mkArgs 3 4
  c <- mkCall MulA $ mkArgs 5 6
  d <- mkCall MulA $ mkArgs 7 8
  e <- mkCall MulA $ mkArgs 9 10
  (a, b, c, d, e) `shouldBe` (2, 12, 30, 56, 90)
  failed


prog2 :: forall c sig m. (Has (Api StackApiA :+: PropertyA :+: QVS c) sig m, WFTypeSpec (BasicSpec c)) => m ()
prog2 = do
  stk <- mkCall CreateA noArgs
  n <- send (QVS @c $ IntRange 0 100)
  mkCall PushA $ mkArgs stk n
  mkCall PeekA (mkArgs stk) `shouldReturn` n
  mkCall SizeA (mkArgs stk) `shouldReturn` 1
  mkCall PopA $ mkArgs stk
  mkCall SizeA (mkArgs stk) `shouldReturn` 1

prog3 :: forall c sig m. (Has (Api StackApiA :+: PropertyA :+: QVS c) sig m, WFTypeSpec (BasicSpec c)) => m ()
prog3 = do
  stk <- mkCall CreateA noArgs
  n <- send (QVS @c $ IntRange 0 100)
  forM_ [1..n] $ \i -> do
    mkCall PushA (mkArgs stk (2 * i))
  mkCall SizeA (mkArgs stk) `shouldReturn` n
  mkCall PeekA (mkArgs stk) `shouldReturn` (2 * n)

runArb :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
runArb = do runGenIO
          . runQVSFromStdin @(BasicSpec Read)
          . runError @PropertyError (fail . show) pure
          . runProperty @PropertyA
          . runApiFFI @ShowApiA
          $ arb @Read

runProg :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
runProg = do runGenIO
          . runError @PropertyError (fail . show) pure
          . runProperty @PropertyA
          . runApiFFI @ArithApiA
          $ prog1

runProg2 :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
runProg2 = do
  x <- runQVSFromStdin @(BasicSpec Read)
     . runError @PropertyError (fail . show) pure
     . runProperty @PropertyA
     . runApiFFI @StackApiA
    --  . runCPRAC @ApiFFIAC @StackApiA  -- TODO
     $ prog3 @Read
  liftIO $ print x
  return ()
