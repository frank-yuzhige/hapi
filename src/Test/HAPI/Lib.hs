{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Test.HAPI.Lib where

import Control.Algebra (Has, type (:+:), send)
import Test.HAPI.Api
    ( HaskellIOCall(..), HasHaskellDef(..), runApi, runApiIO )
import Test.HAPI.Property (PropertyA, runProperty, shouldBe, PropertyError)
import Text.Read (readMaybe)
import Control.Carrier.Error.Either (Catch, Error, Throw)
import Control.Monad.IO.Class (MonadIO)

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

instance HaskellIOCall ShowApiA where
  readOut (StrA _) = readMaybe
  showArgs = show

instance HasHaskellDef ArithApiA where
  evalHaskell (AddA a b) = a + b
  evalHaskell (SubA a b) = a - b
  evalHaskell (MulA a b) = a * b
  evalHaskell (NegA a)   = -a

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
show3Plus5Is8 :: Has (ArithApiA :+: ShowApiA :+: PropertyA) sig m => m Bool
show3Plus5Is8 = do
  x <- addA 3 5
  x <- mulA 5 x
  x <- strA x
  x `shouldBe` "40"

prop :: (Has (Throw PropertyError) sig m , MonadIO m, MonadFail m) => m (Either PropertyError Bool)
prop = runProperty @PropertyA
     . runApi @ArithApiA
     . runApiIO @ShowApiA
     $ show3Plus5Is8
