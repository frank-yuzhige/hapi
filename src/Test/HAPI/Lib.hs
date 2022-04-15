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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Test.HAPI.Lib where

import Control.Algebra ( Has, type (:+:), send, Algebra )
import Test.HAPI.Api ( HaskellIOCall(..), HasHaskellDef(..), HasForeignDef (evalForeign), ApiDefinition, ApiTrace (ApiTrace), newVPtr, getPtr, ApiError )
import Test.HAPI.Effect.Api (runApi, runApiIO, runApiFFI, ApiFFIAC (ApiFFIAC), Api, mkCall)
import Test.HAPI.Effect.Property (PropertyA, runProperty, shouldBe, PropertyError, PropertyAC (..), failed, shouldReturn)
import Text.Read (readMaybe)
import Control.Carrier.Error.Church (Catch, Error, Throw, catchError, runError, ErrorC)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad (void, replicateM, forM, forM_)
import Test.HAPI.Effect.Gen (GenA, liftGenA, GenAC (runGenAC), anyVal, runGenIO, suchThat, chooseA)
import Test.QuickCheck.GenT (MonadGen(liftGen), runGenT)
import Test.QuickCheck (Arbitrary(arbitrary), generate)
import Test.HAPI.FFI (add, sub, mul, neg, str, Stack, createStack, pushStack, popStack, peekStack, getStackSize, FFIO (unFFIO), ffi)
import Control.Effect.Labelled (Labelled(Labelled))
import Foreign.C (peekCString)
import Test.HAPI.Effect.QVS (QVS (QVS), QVSFuzzArbitraryAC (runQVSFuzzArbitraryAC), QVSFromStdinAC (runQVSFromStdinAC))
import Test.QuickCheck.Random (QCGen(QCGen))
import Data.Data (Proxy (Proxy))
import Foreign (Ptr)
import Data.SOP (NP (Nil, (:*)), All)
import Test.HAPI.DataType (BasicSpec, WFTypeSpec, type (:&:))
import Data.HList (HList(HNil, HCons))
import Test.HAPI.Args (args, noArgs, pattern (::*), Attribute (IntRange, Value, Anything, Get))
import Control.Carrier.Writer.Strict (runWriter)
import Control.Carrier.Trace.Printing (runTrace)
import Control.Carrier.State.Strict (runState, put, modify, gets)
import Test.HAPI.PState (PState(PState), empty)
import Test.HAPI.VPtr (VPtr, VPtrTable, storePtr, ptr2VPtr, vPtr2Ptr)
import Test.HAPI.Effect.FF (ff, runFFAC)
import Control.Monad.Trans.Class (lift)
import Control.Carrier.Fresh.Strict (runFresh)
import Test.HAPI.AASTG.Core (AASTG (AASTG), Edge (Update, APICall), synthStub, newAASTG)
import Control.Effect.Sum (Members)
import Test.HAPI.AASTG.Analysis.TypeCheck (typeCheck)
import Test.HAPI.AASTG.Analysis.PathExtra (getPathMap)
import Test.HAPI.AASTG.Analysis.Path (outPaths)


data ArithApiA :: ApiDefinition where
  AddA :: ArithApiA '[Int, Int] Int
  SubA :: ArithApiA '[Int, Int] Int
  MulA :: ArithApiA '[Int, Int] Int
  NegA :: ArithApiA '[Int, Int] Int

data ShowApiA :: ApiDefinition where
  StrA :: ShowApiA '[Int] String

data StackApiA :: ApiDefinition where
  CreateA :: StackApiA '[]                (VPtr Stack)
  PushA   :: StackApiA '[VPtr Stack, Int] ()
  PopA    :: StackApiA '[VPtr Stack]      ()
  PeekA   :: StackApiA '[VPtr Stack]      Int
  SizeA   :: StackApiA '[VPtr Stack]      Int

deriving instance Show (ArithApiA p a)
deriving instance Show (ShowApiA p a)
deriving instance Show (StackApiA p a)
deriving instance Eq (ArithApiA p a)
deriving instance Eq (ShowApiA p a)
deriving instance Eq (StackApiA p a)

instance HasHaskellDef ShowApiA where
  evalHaskell StrA [args|a|] = show a

instance HasForeignDef ShowApiA where
  evalForeign StrA [args|a|] = do
    ptr <- ffi $ str (fromIntegral a)
    liftIO $ peekCString ptr

instance HaskellIOCall ShowApiA where
  readOut StrA = readMaybe


instance HasHaskellDef ArithApiA where
  evalHaskell AddA [args|a b|] = a + b
  evalHaskell SubA [args|a b|] = a - b
  evalHaskell MulA [args|a b|] = a * b
  evalHaskell NegA [args|a b|] = -a

instance HasForeignDef ArithApiA where
  evalForeign AddA [args|a b|] = fromIntegral <$> ffi (add (fromIntegral a) (fromIntegral b))
  evalForeign SubA [args|a b|] = fromIntegral <$> ffi (sub (fromIntegral a) (fromIntegral b))
  evalForeign MulA [args|a b|] = fromIntegral <$> ffi (mul (fromIntegral a) (fromIntegral b))
  evalForeign NegA [args|a b|] = fromIntegral <$> ffi (neg (fromIntegral a))

instance HaskellIOCall ArithApiA where
  readOut AddA = readMaybe
  readOut SubA = readMaybe
  readOut MulA = readMaybe
  readOut NegA = readMaybe

instance HasForeignDef StackApiA where
  evalForeign CreateA [args||]      = ffi createStack >>= newVPtr
  evalForeign PushA   [args|ptr n|] = do
    p <- getPtr ptr
    ffi $ pushStack p (fromIntegral n)
  evalForeign PopA    [args|ptr  |] = ffi . popStack =<< getPtr ptr
  evalForeign PeekA   [args|ptr  |] = fmap fromIntegral (ffi . peekStack    =<< getPtr ptr)
  evalForeign SizeA   [args|ptr  |] = fmap fromIntegral (ffi . getStackSize =<< getPtr ptr)

-- | Example program, calling arithmetic and show API
show3Plus5Is8 :: Has (Api ArithApiA :+: Api ShowApiA :+: PropertyA) sig m => m ()
show3Plus5Is8 = do
  x <- mkCall AddA [args|10 20|]
  x <- mkCall SubA [args|(-10050) x|]
  x <- mkCall StrA [args|x|]
  x `shouldBe` "40"

arb :: forall c sig m. (Has (Api ShowApiA :+: PropertyA :+: QVS c) sig m, WFTypeSpec (BasicSpec c))
    => m ()
arb = do
  a <- send (QVS @c $ IntRange 0 100)
  b <- send (QVS @c $ IntRange 0 100)
  mkCall StrA [args|a|] `shouldReturn` show a
  mkCall StrA [args|b|] `shouldReturn` show b
  mkCall StrA [args|a|] `shouldReturn` show a
  failed

prog1 :: Has (Api ArithApiA :+: PropertyA) sig m => m ()
prog1 = do
  a <- mkCall MulA [args|1 2|]
  b <- mkCall MulA [args|3 4|]
  c <- mkCall MulA [args|5 6|]
  d <- mkCall MulA [args|7 8|]
  e <- mkCall MulA [args|9 10|]
  (a, b, c, d, e) `shouldBe` (2, 12, 30, 56, 90)
  failed


prog2 :: forall c sig m. (Has (Api StackApiA :+: PropertyA :+: QVS c) sig m, WFTypeSpec (BasicSpec c)) => m ()
prog2 = do
  stk <- mkCall CreateA noArgs
  n <- send (QVS @c $ IntRange 0 100)
  mkCall PushA [args|stk n|]
  mkCall PeekA [args|stk|] `shouldReturn` n
  mkCall SizeA [args|stk|] `shouldReturn` 1
  mkCall PopA  [args|stk|]
  mkCall SizeA [args|stk|] `shouldReturn` 1

prog3 :: forall c sig m. (Has (Api StackApiA :+: PropertyA :+: QVS c) sig m, WFTypeSpec (BasicSpec c)) => m ()
prog3 = do
  stk <- mkCall CreateA noArgs
  n <- send (QVS @c $ IntRange 0 100)
  forM_ [1..n] $ \i -> do
    mkCall PushA [args|stk 2*i|]
  mkCall SizeA [args|stk|] `shouldReturn` n
  mkCall PeekA [args|stk|] `shouldReturn` (2 * n)

-- runArb :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
-- runArb = do runGenIO
--           . runQVSFromStdinAC
--           . runError @PropertyError (fail . show) pure
--           . runProperty @PropertyA
--           . runApiFFI @ShowApiA
--           $ arb @Read

-- runProg :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
-- runProg = do runGenIO
--           . runError @PropertyError (fail . show) pure
--           . runProperty @PropertyA
--           . runApiFFI @ArithApiA
--           $ prog1

runProg2 :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
runProg2 = do
  -- let x = prog3 @Arbitrary
  -- let x1 = runApiFFI @StackApiA x
  -- let x2 = runError @ApiError (fail . show) pure x1
  -- let x3 = runFFAC x2
  -- let x4 = runFresh 0 x3
  -- let x5 = runTrace x4
  -- let x6 = runProperty @PropertyA x5
  -- let x7 = runError @PropertyError (fail . show) pure x6
  -- let x8 = runWriter @(ApiTrace StackApiA) x7
  -- let x9 = runQVSFuzzArbitraryAC x8
  -- let x10 = runState empty x9
  -- x <- runGenIO x10
  x <- runGenIO
     . runWriter @(ApiTrace StackApiA)
     . runTrace
     . runFresh 0
     . runState empty
     . runFFAC
     . runError @PropertyError (fail . show) pure
     . runProperty @PropertyA
     . runError @ApiError (fail . show) pure
     . runApiFFI @StackApiA
     . runQVSFuzzArbitraryAC
     $ prog3 @Arbitrary
  liftIO $ print $ fst x
  return ()


graph1 :: forall c. (c Double, c Int) => AASTG (ArithApiA) c
graph1 = newAASTG [
    Update  0 1 "a" (Value @Int 10)
  , Update  1 2 "b" (Anything @Int)
  , Update  2 3 "x" (Anything @Int)
  , APICall 3 4 (Just "a") AddA (Get "a" :* Get "b"  :* Nil)
  , APICall 3 5 (Just "a") SubA (Get "a" :* Anything :* Nil)
  , APICall 4 6 (Just "b") AddA (Get "a" :* Get "a"  :* Nil)
  , APICall 5 6 (Just "b") AddA (Get "a" :* Get "a"  :* Nil)
  ]

graph2 :: forall c. (c Int) => AASTG (ArithApiA) c
graph2 = newAASTG [
    Update  @Int 0 1 "a" (Value 10)
  , Update  @Int 1 2 "b" Anything
  , APICall @Int 2 3 (Just "a") AddA (Get "a" :* Get "b"  :* Nil)
  , APICall @Int 2 4 (Just "a") SubA (Get "a" :* Anything :* Nil)
  , APICall @Int 3 5 (Just "b") AddA (Get "a" :* Get "a"  :* Nil)
  , APICall @Int 4 5 (Just "b") AddA (Get "a" :* Get "a"  :* Nil)
  ]

x = getPathMap (graph1 @Arbitrary)
y = outPaths 0 (graph1 @Arbitrary)

runGraph1 :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
runGraph1 = do
  forM_ (synthStub (graph1 @Arbitrary)) $ \stub -> do
    x <- runGenIO
       . runWriter @(ApiTrace ArithApiA)
       . runTrace
       . runFresh 0
       . runState empty
       . runFFAC
       . runError @PropertyError (fail . show) pure
       . runProperty @PropertyA
       . runError @ApiError (fail . show) pure
       . runApiFFI @ArithApiA
       . runQVSFuzzArbitraryAC
       $ stub
    liftIO $ print $ fst x
