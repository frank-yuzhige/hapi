{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Test.HAPI.Lib where

import Control.Algebra ( Has, type (:+:), send, Algebra )
import Test.HAPI.Api
    ( HaskellIOCall(..), HasHaskellDef(..), runApi, runApiIO, HasForeignDef (evalForeign), runApiFFI )
import Test.HAPI.Property (PropertyA, runProperty, shouldBe, PropertyError, PropertyAC (runPropertyTypeAC), failed)
import Text.Read (readMaybe)
import Control.Carrier.Error.Church (Catch, Error, Throw, catchError, runError, ErrorC)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad (void)
import Test.HAPI.GenT (GenA, liftGenA, GenAC (runGenAC), anyVal, runGenIO)
import Test.QuickCheck.GenT (MonadGen(liftGen), runGenT)
import Test.QuickCheck (Arbitrary(arbitrary), generate)
import Test.HAPI.GenT (suchThat, chooseA)
import Test.HAPI.FFI (add, sub, mul, neg, str)
import Control.Effect.Labelled (Labelled(Labelled))
import Foreign.C (peekCString)

data ArithApiA (m :: * -> *) a where
  AddA :: Int -> Int -> ArithApiA m Int
  SubA :: Int -> Int -> ArithApiA m Int
  MulA :: Int -> Int -> ArithApiA m Int
  NegA :: Int -> ArithApiA m Int

data ShowApiA (m :: * -> *) a where
  StrA :: Int -> ShowApiA m String

deriving instance Show (ArithApiA m a)
deriving instance Show (ShowApiA m a)

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

arb :: Has (ShowApiA :+: PropertyA :+: GenA) sig m => m ()
arb = do
  a <- chooseA (10000000, 20000000)
  b <- chooseA (10000000, 20000000)
  x <- strA a
  x `shouldBe` show a
  y <- strA b
  y `shouldBe` show b
  x <- strA a
  x `shouldBe` show a

prog1 :: Has (ArithApiA :+: PropertyA :+: GenA) sig m => m ()
prog1 = do
  a <- mulA 1 2
  b <- mulA 3 4
  c <- mulA 5 6
  d <- mulA 7 8
  e <- mulA 9 10
  (a, b, c, d, e) `shouldBe` (2, 12, 30, 56, 90)
  failed


runArb :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
runArb = do runGenIO
          . runError @PropertyError (fail . show) pure
          . runProperty @PropertyA
          . runApiFFI @ShowApiA
          $ arb

runProg :: forall m sig. (MonadIO m, MonadFail m, Algebra sig m) => m ()
runProg = do runGenIO
          . runError @PropertyError (fail . show) pure
          . runProperty @PropertyA
          . runApiFFI @ArithApiA
          $ prog1
