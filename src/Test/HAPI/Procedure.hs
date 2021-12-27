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


class HaskellFnDef (def :: (* -> *) -> * -> *) where
  evalHaskell :: def m a -> a

class HaskellIOCall (def :: (* -> *) -> * -> *) where
  showArgs :: def m a -> String
  readOut :: def m a -> String -> Maybe a

data ProcedureA (m :: * -> *) a where
  AddA :: Int -> Int -> ProcedureA m Int
  SubA :: Int -> Int -> ProcedureA m Int
  MulA :: Int -> Int -> ProcedureA m Int
  NegA :: Int -> ProcedureA m Int
  StrA :: Int -> ProcedureA m String

deriving instance Show (ProcedureA m a)

instance HaskellFnDef ProcedureA where
  evalHaskell (AddA a b) = a + b
  evalHaskell (SubA a b) = a - b
  evalHaskell (MulA a b) = a * b
  evalHaskell (NegA a)   = -a
  evalHaskell (StrA a)   = show a

instance HaskellIOCall ProcedureA where
  readOut (StrA _) = readMaybe
  readOut (AddA _ _) = readMaybe
  readOut (SubA _ _) = readMaybe
  readOut (MulA _ _) = readMaybe
  readOut (NegA _) = readMaybe
  showArgs = show

addA, subA, mulA :: Has ProcedureA sig m => Int -> Int -> m Int
addA a b = send $ AddA a b
subA a b = send $ SubA a b
mulA a b = send $ MulA a b

negA :: Has ProcedureA sig m => Int -> m Int
negA a = send $ NegA a

strA :: Has ProcedureA sig m => Int -> m String
strA a = send $ StrA a

-- | Encode procedure's type into its underlying interpretation to ensure functional dependency for Algebra holds
newtype ProcedureAC (proc :: (* -> *) -> * -> *) m a = ProcedureAC {runProcedureAC :: ReaderC () m a}
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runProcedure :: ProcedureAC proc m a -> m a
runProcedure = runReader () . runProcedureAC

newtype ProcedureRpcAC (proc :: (* -> *) -> * -> *) m a = ProcedureRpcAC { runProcedureRpcAC :: ReaderC () m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runProcedureRpc :: ProcedureRpcAC proc m a -> m a
runProcedureRpc = runReader () . runProcedureRpcAC

-- | If the procedure can map to relevant haskell functions, then it can be interpreted
instance (Algebra sig m, HaskellFnDef proc) => Algebra (proc :+: sig) (ProcedureAC proc m) where
  alg hdl sig ctx = ProcedureAC $ case sig of
    L procedure -> return (ctx $> evalHaskell procedure)
    R other -> alg (runProcedureAC . hdl) (R other) ctx

instance (Algebra sig m, MonadIO m, MonadFail m, HaskellIOCall proc) => Algebra (proc :+: sig) (ProcedureRpcAC proc m) where
  alg hdl sig ctx = ProcedureRpcAC $ case sig of
    L procedure -> do
      liftIO $ putStrLn $ showArgs procedure
      out <- liftIO (readOut procedure <$> getLine)
      case out of
        Nothing -> fail "Parse error"
        Just o  -> return (ctx $> o)
    R other -> alg (runProcedureRpcAC . hdl) (R other) ctx


show3Plus5Min2 :: Has ProcedureA sig m => m String
show3Plus5Min2 = do
  eight <- addA 3 5
  subA eight 2 >>= strA

x, y :: IO String
x = runReader () $ runProcedureRpcAC @ProcedureA show3Plus5Min2
y = runReader () $ runProcedureAC @ProcedureA show3Plus5Min2

data PropertyA (m :: * -> *) a where
  EqA :: Eq a => a -> a -> PropertyA m Bool

(===) :: (Eq a, Has PropertyA sig m) => a -> a -> m Bool
a === b = send $ EqA a b

newtype PropertyAC (prop :: (* -> *) -> * -> *) m a = PropertyAC { runPropertyAC :: ReaderC () m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runProperty :: PropertyAC prop m a -> m a
runProperty = runReader () . runPropertyAC

class EvalProperty (prop :: (* -> *) -> * -> *) where
  assertProp :: prop m a -> a

instance EvalProperty PropertyA where
  assertProp (EqA a b) = a == b

instance (Algebra sig m, EvalProperty prop) => Algebra (prop :+: sig) (PropertyAC prop m) where
  alg hdl sig ctx = PropertyAC $ case sig of
     L prop -> return $ ctx $> assertProp prop
     R other -> alg (runPropertyAC . hdl) (R other) ctx

show3Plus5Is8 :: Has (ProcedureA :+: PropertyA) sig m => m Bool
show3Plus5Is8 = do
  x <- addA 3 5
  x' <- strA x
  let y = "8"
  x' === y

prop :: IO Bool
prop = runProperty @PropertyA $ runProcedureRpc @ProcedureA show3Plus5Is8
