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
import Test.HAPI.Args (Args, showArgs)
import Data.Tuple.HList (HLst (toHList))
import Test.HAPI.Common (Fuzzable)
import Data.SOP (All)


type ApiDefinition = [Type] -> Type -> Type

-- | Name of an API call
class ApiName (api :: ApiDefinition) where
  apiName :: api p a -> String

instance {-# OVERLAPPABLE #-}
  (forall p a. Show (api p a)) => ApiName api where
  apiName = show

-- | Given API spec has a direct mapping to its haskell pure implementation
class HasHaskellDef (api :: ApiDefinition) where
  evalHaskell :: api p a -> Args p -> a

-- | Given API spec has a FFI
class HasForeignDef (api :: ApiDefinition) where
  evalForeign :: api p a -> Args p -> FFIO a

-- | [DEBUG] Given API spec can be debugged (using Haskell IO to mock input/output)
class (ApiName api) => HaskellIOCall (api :: ApiDefinition) where
  readOut  :: api p a -> String -> Maybe a

data ApiTraceEntry (api :: ApiDefinition) where
  CallOf :: All Show p => api p a -> Args p -> ApiTraceEntry api

instance ApiName api => Show (ApiTraceEntry api) where
  show (CallOf api args) = apiName api <> showArgs args

newtype ApiTrace (api :: ApiDefinition) = ApiTrace { apiTrace2List :: [ApiTraceEntry api] }
  deriving (Semigroup, Monoid)

instance Show (ApiTraceEntry api) => Show (ApiTrace api) where
  show (ApiTrace xs) = "ApiTrace " <> show xs
