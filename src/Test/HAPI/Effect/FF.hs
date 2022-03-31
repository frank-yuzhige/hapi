{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.HAPI.Effect.FF where
import Test.HAPI.FFI (FFIO (unFFIO))
import Control.Algebra (Has, send, Algebra, type (:+:) (L, R))
import Control.Monad.IO.Class
import Control.Effect.Labelled (Algebra(alg))
import Data.Functor (($>))

data FF (m :: * -> *) a where
  FF :: FFIO a -> FF m a

ff :: Has FF sig m => FFIO a -> m a
ff = send . FF

newtype FFAC m a = FFAC { runFFAC :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

instance (Algebra sig m, MonadIO m) => Algebra (FF :+: sig) (FFAC m) where
  alg hdl sig ctx = FFAC $ case sig of
    L (FF io) -> do
      x <- liftIO $ unFFIO io
      return (ctx $> x)
    R other -> alg (runFFAC . hdl) other ctx


