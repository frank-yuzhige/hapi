{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.HAPI.Procedure where

import Control.Algebra (Has, alg, send, Algebra, (:+:) (L, R), Handler)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Data (Proxy (Proxy))
import Control.Carrier.State.Church (StateC(..), put, execState)
import Control.Carrier.Cull.Church (MonadPlus)
import Data.Functor (($>))
import Data.Void (Void)
import Data.Kind (Constraint)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.Writer.Strict (WriterC, tell)
import Text.Read (readMaybe)


type ApiDefinition = (* -> *) -> * -> *
type PropertyType = (* -> *) -> * -> *

class HasHaskellDef (api :: ApiDefinition) where
  evalHaskell :: api m a -> a

class HaskellIOCall (api :: ApiDefinition) where
  showArgs :: api m a -> String
  readOut :: api m a -> String -> Maybe a

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

addA, subA, mulA :: Has ArithApiA sig m => Int -> Int -> m Int
addA a b = send $ AddA a b
subA a b = send $ SubA a b
mulA a b = send $ MulA a b

negA :: Has ArithApiA sig m => Int -> m Int
negA a = send $ NegA a

strA :: Has ShowApiA sig m => Int -> m String
strA a = send $ StrA a

-- | Encode api call's type into its underlying interpretation to ensure functional dependency for Algebra holds
newtype ApiAC (api :: ApiDefinition) m a = ApiAC { runApiAC :: ReaderC () m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApi :: ApiAC proc m a -> m a
runApi = runReader () . runApiAC

newtype ApiRpcAC (api :: ApiDefinition) m a = ApiRpcAC { runApiRpcAC :: ReaderC () m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runApiRpc :: ApiRpcAC proc m a -> m a
runApiRpc = runReader () . runApiRpcAC

-- | If the api call can map to relevant haskell functions, then it can be interpreted
instance (Algebra sig m, HasHaskellDef api) => Algebra (api :+: sig) (ApiAC api m) where
  alg hdl sig ctx = ApiAC $ case sig of
    L call -> return (ctx $> evalHaskell call)
    R other -> alg (runApiAC . hdl) (R other) ctx

instance (Algebra sig m, MonadIO m, MonadFail m, HaskellIOCall proc) => Algebra (proc :+: sig) (ApiRpcAC proc m) where
  alg hdl sig ctx = ApiRpcAC $ case sig of
    L call -> do
      liftIO $ putStrLn $ showArgs call
      out <- liftIO (readOut call <$> getLine)
      case out of
        Nothing -> fail "Parse error"
        Just o  -> return (ctx $> o)
    R other -> alg (runApiRpcAC . hdl) (R other) ctx

data PropertyTypeA (m :: * -> *) a where
  ShouldBeA :: Eq a => a -> a -> PropertyTypeA m Bool

shouldBe :: (Eq a, Has PropertyTypeA sig m) => a -> a -> m Bool
shouldBe a b = send $ ShouldBeA a b

newtype PropertyTypeAC (prop :: PropertyType) m a = PropertyTypeAC { runPropertyTypeAC :: ReaderC () m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runPropertyType :: PropertyTypeAC prop m a -> m a
runPropertyType = runReader () . runPropertyTypeAC

class EvalPropertyType (prop :: PropertyType) where
  evalPropertyType :: prop m a -> a

instance EvalPropertyType PropertyTypeA where
  evalPropertyType (ShouldBeA a b) = a == b

instance (Algebra sig m, EvalPropertyType prop) => Algebra (prop :+: sig) (PropertyTypeAC prop m) where
  alg hdl sig ctx = PropertyTypeAC $ case sig of
    L prop  -> return $ ctx $> evalPropertyType prop
    R other -> alg (runPropertyTypeAC . hdl) (R other) ctx

show3Plus5Is8 :: Has (ArithApiA :+: ShowApiA :+: PropertyTypeA) sig m => m Bool
show3Plus5Is8 = do
  x <- addA 3 5
  x' <- strA x
  let y = "8"
  x' `shouldBe` y

prop :: IO Bool
prop = runPropertyType @PropertyTypeA
     $ runApiRpc @ArithApiA
     $ runApi @ShowApiA
     $ show3Plus5Is8
