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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.Api where

import Control.Algebra (Has, alg, send, Algebra, (:+:) (L, R), Handler)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Carrier.State.Church (StateC(..), put, execState)
import Control.Carrier.Cull.Church (MonadPlus)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.Writer.Strict (WriterC, tell, runWriter)
import Data.Functor (($>))
import Data.Void (Void)
import Data.Kind (Constraint, Type)
import Text.Read (readMaybe)
import Control.Effect.Labelled (Labelled (Labelled), runLabelled)
import Test.HAPI.FFI (FFIO(FFIO, unFFIO))
import Control.Monad.Trans.Identity (IdentityT (runIdentityT))
import Control.Monad.Trans.Class (MonadTrans (lift))
import Data.HList (HList (HNil, HCons), HBuild')
import Test.HAPI.Args (Args)
import Data.Tuple.HList (HLst (toHList))
import Test.HAPI.Common (Fuzzable)


type ApiDefinition = [Type] -> Type -> Type

-- | Given API spec has a direct mapping to its haskell pure implementation
class HasHaskellDef (api :: ApiDefinition) where
  evalHaskell :: api p a -> HList p -> a

-- | Given API spec has a FFI
class HasForeignDef (api :: ApiDefinition) where
  evalForeign :: api p a -> HList p -> FFIO a

-- | [DEBUG] Given API spec can be debugged (using Haskell IO to mock input/output)
class HaskellIOCall (api :: ApiDefinition) where
  showArgs :: api p a -> String
  readOut  :: api p a -> String -> Maybe a



-- -- | Call path record
-- class HasCallPath (api :: ApiDefinition) where
--   showCall :: api p a -> String

-- newtype CPRAC (apiAC :: ApiDefinition -> (* -> *) -> * -> *) (api :: ApiDefinition) m a = CPRAC {
--   runCPRAC :: WriterC [String] (apiAC api m) a
-- }  deriving (Functor, Applicative, Monad, MonadIO)



-- instance (Algebra sig m, Algebra (api p api :+: sig) (apiAC api m), HasCallPath api) => Algebra (api p api :+: sig) (CPRAC apiAC api m) where
--   alg hdl sig ctx = CPRAC $ case sig of
--     L (MkCall call) -> do
--       tell @[String] [showCall call]
--       alg (runCPRAC . hdl) (R (L call)) ctx
--       return undefined  -- TODO
--     R other -> alg (runCPRAC . hdl) (R (R other)) ctx

