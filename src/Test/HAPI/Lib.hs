{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

module Test.HAPI.Lib where

import Control.Algebra ( Has, type (:+:), send, Algebra )
import Test.HAPI.Api
    ( HaskellIOCall(..), HasHaskellDef(..), runApi, runApiIO, HasForeignDef (evalForeign), runApiFFI, CPRAC (runCPRAC), ApiFFIAC (ApiFFIAC) )
import Test.HAPI.Property (PropertyA, runProperty, shouldBe, PropertyError, PropertyAC (..), failed, shouldReturn)
import Text.Read (readMaybe)
import Control.Carrier.Error.Church (Catch, Error, Throw, catchError, runError, ErrorC)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad (void, replicateM, forM, forM_)
import Test.HAPI.GenT (GenA, liftGenA, GenAC (runGenAC), anyVal, runGenIO)
import Test.QuickCheck.GenT (MonadGen(liftGen), runGenT)
import Test.QuickCheck (Arbitrary(arbitrary), generate)
import Test.HAPI.GenT (suchThat, chooseA)
import Test.HAPI.FFI (add, sub, mul, neg, str, Stack, createStack, pushStack, popStack, peekStack, getStackSize)
import Control.Effect.Labelled (Labelled(Labelled))
import Foreign.C (peekCString)
import Test.HAPI.QVS (QVS (IntRange), QVSFuzzArbitraryCA (runQVSFuzzArbitraryCA), QVSFromStdin (runQVSFromStdin))
import Test.QuickCheck.Random (QCGen(QCGen))
import Data.Data (Proxy (Proxy))
import Foreign (Ptr)
import Test.HAPI.Constraint (type (:>>>:))
import Test.HAPI.DataType (BasicSpec, WFTypeSpec, type (:&:))

data ArithApiA (m :: * -> *) a where
  AddA :: Int -> Int -> ArithApiA m Int
  SubA :: Int -> Int -> ArithApiA m Int
  MulA :: Int -> Int -> ArithApiA m Int
  NegA :: Int -> ArithApiA m Int

data ShowApiA (m :: * -> *) a where
  StrA :: Int -> ShowApiA m String

data StackApiA (m :: * -> *) a where
  CreateA :: StackApiA m (Ptr Stack)
  PushA   :: Ptr Stack -> Int -> StackApiA m ()
  PopA    :: Ptr Stack -> StackApiA m ()
  PeekA   :: Ptr Stack -> StackApiA m Int
  SizeA   :: Ptr Stack -> StackApiA m Int

deriving instance Show (ArithApiA m a)
deriving instance Show (ShowApiA m a)
deriving instance Show (StackApiA m a)

instance HasHaskellDef ShowApiA where
  evalHaskell (StrA a) = show a

instance HasForeignDef ShowApiA where
  evalForeign (StrA a) = do
    ptr <- str (fromIntegral a)
    liftIO $ peekCString ptr

instance HaskellIOCall ShowApiA where
  readOut (StrA _) = readMaybe
  showArgs = show

instance HasHaskellDef ArithApiA where
  evalHaskell (AddA a b) = a + b
  evalHaskell (SubA a b) = a - b
  evalHaskell (MulA a b) = a * b
  evalHaskell (NegA a)   = -a

instance HasForeignDef ArithApiA where
  evalForeign (AddA a b) = fromIntegral <$> add (fromIntegral a) (fromIntegral b)
  evalForeign (SubA a b) = fromIntegral <$> sub (fromIntegral a) (fromIntegral b)
  evalForeign (MulA a b) = fromIntegral <$> mul (fromIntegral a) (fromIntegral b)
  evalForeign (NegA a)   = fromIntegral <$> neg (fromIntegral a)

instance HaskellIOCall ArithApiA where
  readOut (AddA _ _) = readMaybe
  readOut (SubA _ _) = readMaybe
  readOut (MulA _ _) = readMaybe
  readOut (NegA _) = readMaybe
  showArgs = show

instance HasForeignDef StackApiA where
  evalForeign CreateA       = createStack
  evalForeign (PushA ptr n) = pushStack ptr (fromIntegral n)
  evalForeign (PopA  ptr)   = popStack  ptr
  evalForeign (PeekA ptr)   = fromIntegral <$> peekStack    ptr
  evalForeign (SizeA ptr)   = fromIntegral <$> getStackSize ptr

-- | Senders
addA, subA, mulA :: Has ArithApiA sig m => Int -> Int -> m Int
addA a b = send $ AddA a b
subA a b = send $ SubA a b
mulA a b = send $ MulA a b

negA :: Has ArithApiA sig m => Int -> m Int
negA a = send $ NegA a

strA :: Has ShowApiA sig m => Int -> m String
strA a = send $ StrA a

-- | Example program, calling arithmetic and show API
show3Plus5Is8 :: Has (ArithApiA :+: ShowApiA :+: PropertyA) sig m => m ()
show3Plus5Is8 = do
  x <- addA 3 5
  x <- subA (-10005) x
  x <- strA x
  x `shouldBe` "40"

prop :: (MonadIO m, MonadFail m, Algebra sig m) => m ()
prop = runError @PropertyError (fail . show) pure
     . runProperty @PropertyA
     . runApiFFI @ArithApiA
     . runApiIO @ShowApiA
     $ show3Plus5Is8

arb :: forall c sig m. (Has (ShowApiA :+: PropertyA :+: QVS (BasicSpec c)) sig m, WFTypeSpec (BasicSpec c))
    => Proxy c
    -> m ()
arb _ = do
  a <- send (IntRange @(BasicSpec c) 0 100)
  b <- send (IntRange @(BasicSpec c) 0 100)
  strA a `shouldReturn` show a
  strA b `shouldReturn` show b
  strA a `shouldReturn` show a
  failed

prog1 :: Has (ArithApiA :+: PropertyA) sig m => m ()
prog1 = do
  a <- mulA 1 2
  b <- mulA 3 4
  c <- mulA 5 6
  d <- mulA 7 8
  e <- mulA 9 10
  (a, b, c, d, e) `shouldBe` (2, 12, 30, 56, 90)
  failed


prog2 :: forall c sig m. (Has (StackApiA :+: PropertyA :+: QVS (BasicSpec c)) sig m, WFTypeSpec (BasicSpec c)) => Proxy c -> m ()
prog2 _ = do
  stk <- send CreateA
  n <- send (IntRange @(BasicSpec c) 0 100)
  send $ PushA stk n
  send (PeekA stk) `shouldReturn` n
  send (SizeA stk) `shouldReturn` 1
  send $ PopA stk
  send (SizeA stk) `shouldReturn` 1

prog3 :: forall c sig m. (Has (StackApiA :+: PropertyA :+: QVS (BasicSpec c)) sig m, WFTypeSpec (BasicSpec c)) => Proxy c -> m ()
prog3 _ = do
  stk <- send CreateA
  n <- send (IntRange @(BasicSpec c) 0 100)
  forM_ [1..n] $ \i -> do
    send $ PushA stk (2 * i)
  send (SizeA stk) `shouldReturn` n
  send (PeekA stk) `shouldReturn` (2 * n)

runArb :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
runArb = do runGenIO
          . runQVSFromStdin @(BasicSpec Read)
          . runError @PropertyError (fail . show) pure
          . runProperty @PropertyA
          . runApiFFI @ShowApiA
          $ arb (Proxy @Read)

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
     $ prog3 (Proxy @Read)
  liftIO $ print x
  return ()
