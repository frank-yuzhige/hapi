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
{-# LANGUAGE LambdaCase #-}

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
import Data.Type.Equality (testEquality, castWith, type (:~:), inner, outer)
import Type.Reflection (typeOf)
import Control.Monad (guard)


-- TODO: make a data class
type ApiError = String

type ApiDefinition = [Type] -> Type -> Type

-- | Given API spec has a FFI
type ForeignA = (State VPtrTable :+: Fresh :+: Error ApiError)

-- | Name of an API call
class (forall p a. Eq (api p a), Typeable api) => ApiName (api :: ApiDefinition) where
  apiName :: api p a -> String

-- | Given API spec has a direct mapping to its haskell pure implementation
class HasHaskellDef (api :: ApiDefinition) where
  evalHaskell :: api p a -> Args p -> a

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

apiEq :: (ApiName api, ApiName api2, Typeable p, Typeable a, Typeable q, Typeable b) => api p a -> api2 q b -> Bool
apiEq a b = case testEquality (typeOf a) (typeOf b) of
  Nothing    -> False
  Just proof -> castWith proof a == b

apiEqProofs :: (ApiName api, ApiName api2, Typeable p, Typeable a, Typeable q, Typeable b) => api p a -> api2 q b -> Maybe (api :~: api2, p :~: q, a :~: b)
apiEqProofs a b = do
  proof <- testEquality (typeOf a) (typeOf b)
  guard $ castWith proof a == b
  let ab = inner proof
  let pq = inner (outer proof)
  let fg = outer (outer proof)
  return (fg, pq, ab)


data (f :$$: g) (p :: [Type]) a
  = ApiL (f p a)
  | ApiR (g p a)
  deriving (Eq)

infixr 4 :$$:

class (ApiName sup) => ApiMember (sub :: ApiDefinition) sup where
  injApi :: sub p a -> sup p a

instance (ApiName t) => ApiMember t t where
  injApi = id
  {-# INLINE injApi #-}

-- | Left-recursion: if @t@ is a ApiMember of @l1 ':$$:' l2 ':$$:' r@, then we can inject it into @(l1 ':$$:' l2) ':$$:' r@ by injection into a right-recursive signature, followed by left-association.
instance {-# OVERLAPPABLE #-}
         ( ApiMember t (l1 :$$: l2 :$$: r)
         , ApiName t
         , ApiName l1
         , ApiName l2
         , ApiName r
         )
      => ApiMember t ((l1 :$$: l2) :$$: r) where
  injApi = reassociateSumL . injApi
  {-# INLINE injApi #-}


-- | Left-occurrence: if @t@ is at the head of a signature, we can inject it in O(1).
instance {-# OVERLAPPABLE #-}
         ( ApiName l
         , ApiName r)
        => ApiMember l (l :$$: r) where
  injApi = ApiL
  {-# INLINE injApi #-}


-- | Right-recursion: if @t@ is a ApiMember of @r@, we can inject it into @r@ in O(n), followed by lifting that into @l ':$$:' r@ in O(1).
instance {-# OVERLAPPABLE #-}
         ( ApiMember l r
         , ApiName l
         , ApiName l'
         , ApiName r)
      => ApiMember l (l' :$$: r) where
  injApi = ApiR . injApi
  {-# INLINE injApi #-}


-- | Reassociate a right-nested sum leftwards.
reassociateSumL :: (l1 :$$: l2 :$$: r) m a -> ((l1 :$$: l2) :$$: r) m a
reassociateSumL = \case
  ApiL l        -> ApiL (ApiL l)
  ApiR (ApiL l) -> ApiL (ApiR l)
  ApiR (ApiR r) -> ApiR r
{-# INLINE reassociateSumL #-}

instance (ApiName f, ApiName g) => ApiName (f :$$: g) where
  apiName (ApiL f) = apiName f
  apiName (ApiR g) = apiName g

instance (HasHaskellDef f, HasHaskellDef g) => HasHaskellDef (f :$$: g) where
  evalHaskell (ApiL f) args = evalHaskell f args
  evalHaskell (ApiR g) args = evalHaskell g args

instance (HasForeignDef f, HasForeignDef g) => HasForeignDef (f :$$: g) where
  evalForeign (ApiL f) args = evalForeign f args
  evalForeign (ApiR g) args = evalForeign g args

type family ApiMembers sub sup :: Constraint where
  ApiMembers (f :$$: g) u = (ApiMembers f u, ApiMembers g u)
  ApiMembers t          u = ApiMember t u


class (ApiName api) => HaskellIOCall (api :: ApiDefinition) where
  readOut  :: api p a -> String -> Maybe a

data ApiTraceEntry (api :: ApiDefinition) where
  CallOf :: All Fuzzable p => api p a -> Args p -> ApiTraceEntry api

instance ApiName api => Show (ApiTraceEntry api) where
  show (CallOf api args) = apiName api <> showArgs args

newtype ApiTrace (api :: ApiDefinition) = ApiTrace { apiTrace2List :: DList (ApiTraceEntry api) }
  deriving (Semigroup, Monoid)

apiTrace :: ApiTraceEntry api -> ApiTrace api
apiTrace = ApiTrace . DL.singleton

instance Show (ApiTraceEntry api) => Show (ApiTrace api) where
  show (ApiTrace xs) = "ApiTrace " <> show xs

instance {-# OVERLAPPABLE #-}
  (forall p a. Show (api p a), forall p a. Eq (api p a), Typeable api) => ApiName api where
  apiName = show

instance {-# OVERLAPPABLE #-} ApiName api => Show (api p a) where
  show = apiName
