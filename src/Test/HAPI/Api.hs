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
import Test.HAPI.VPtr (VPtr (VPtr), VPtrTable (VPtrTable), ptr2VPtr, storePtr, vPtr2Ptr)
import Foreign (Ptr)
import Control.Effect.State (State, modify, gets)
import Control.Effect.Fail (Fail)
import Control.Carrier.Fresh.Church (Fresh, fresh)
import Data.Data (Typeable)
import Test.HAPI.Effect.FF (FF)
import Control.Effect.Error (Error, throwError)
import Data.DList (DList)
import qualified Data.DList as DL


-- TODO: make a data class
type ApiError = String

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
type ForeignA = (State VPtrTable :+: Fresh :+: Error ApiError)

class HasForeignDef (api :: ApiDefinition) where
  evalForeign :: (Has ForeignA sig m, MonadIO m) => api p a -> Args p -> m a

newVPtr :: forall t m sig. (Typeable t, Has ForeignA sig m, MonadIO m) => Ptr t -> m (VPtr t)
newVPtr p = do
  i <- fresh
  let name = "p" <> show i
  modify @VPtrTable (storePtr name p)
  a <- gets @VPtrTable (ptr2VPtr p)
  case a of
    Nothing -> throwError "Should not be here"
    Just vp -> return vp

getPtr :: forall t m sig. (Typeable t, Has ForeignA sig m, MonadIO m) => VPtr t -> m (Ptr t)
getPtr v = do
  p <- gets @VPtrTable (vPtr2Ptr v)
  case p of
    Nothing -> throwError "Ptr not in there"
    Just ptr -> return ptr

-- | [DEBUG] Given API spec can be debugged (using Haskell IO to mock input/output)
class (ApiName api) => HaskellIOCall (api :: ApiDefinition) where
  readOut  :: api p a -> String -> Maybe a

data ApiTraceEntry (api :: ApiDefinition) where
  CallOf :: All Show p => api p a -> Args p -> ApiTraceEntry api

instance ApiName api => Show (ApiTraceEntry api) where
  show (CallOf api args) = apiName api <> showArgs args

newtype ApiTrace (api :: ApiDefinition) = ApiTrace { apiTrace2List :: DList (ApiTraceEntry api) }
  deriving (Semigroup, Monoid)

apiTrace :: ApiTraceEntry api -> ApiTrace api
apiTrace = ApiTrace . DL.singleton

instance Show (ApiTraceEntry api) => Show (ApiTrace api) where
  show (ApiTrace xs) = "ApiTrace " <> show xs
