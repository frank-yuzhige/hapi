{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Test.HAPI.Api where

import Control.Algebra (Has, alg, send, Algebra, (:+:) (L, R), Handler)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Carrier.State.Church (StateC(..), put, execState, runState)
import Control.Carrier.Cull.Church (MonadPlus)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.Writer.Strict (WriterC, tell, runWriter)
import Data.Functor (($>))
import Data.Void (Void)
import Data.Kind (Constraint, Type)
import Text.Read (readMaybe)
import Control.Effect.Labelled (Labelled (Labelled), runLabelled, HasLabelled, sendLabelled)
import Control.Monad.Trans.Identity (IdentityT (runIdentityT))
import Control.Monad.Trans.Class (MonadTrans (lift))
import Data.HList (HList (HNil, HCons), HBuild')
import Test.HAPI.Args (Args, ArgPattern, args2Pat)
import Data.Tuple.HList (HLst (toHList))
import Test.HAPI.Common (Fuzzable, ErrorMsg)
import Data.SOP (All, NP (..), Compose, K (K), I (..))
import Test.HAPI.VPtr (VPtr (VPtr), VPtrTable (VPtrTable), ptr2VPtr, storePtr, vPtr2Ptr)
import Foreign (Ptr)
import Control.Effect.State (State, modify, gets, state)
import Control.Effect.Fail (Fail)
import Control.Carrier.Fresh.Church (Fresh (Fresh), fresh, runFresh, FreshC)
import Data.Data (Typeable)
import Control.Effect.Error (Error, throwError)
import Data.DList (DList)
import Data.Type.Equality (testEquality, castWith, type (:~:), inner, outer)
import Type.Reflection (typeOf, typeRep)
import Control.Monad (guard)
import Control.Carrier.Error.Church (runError, ErrorC)
import qualified Data.DList     as DL
import qualified Test.HAPI.VPtr as VP
import Text.Casing (quietSnake)
import Data.TypeRepMap (TypeRepMap)
import qualified Data.TypeRepMap as TM
import Data.HashMap.Internal.Array (map')
import Text.Printf (printf)


-- TODO: make a data class
data ApiError = ApiError
  { errorApiWithArgs :: String
  , apiErrorCause    :: ErrorMsg
  }

type ApiDefinition = [Type] -> Type -> Type

type ValidApiDef api = (HasForeignDef api, ApiName api)

-- | Given API spec has a FFI
type HasForeign sig m =
  ( Has (State ApiMetasState :+: Error ApiError) sig m
  , HasLabelled F Fresh sig m
  , MonadIO m)

-- | Local Foreign Label
data F

-- | "API a la carte". Using generalized DTC to group set of APIs.
data (f :$$: g) (p :: [Type]) a
  = ApiL (f p a)
  | ApiR (g p a)
  deriving (Eq)

infixr 4 :$$:

data ApiMetaAttribute = EXTERNAL_PURE
  deriving (Eq, Ord, Show, Enum)

type family ApiEvalType (p :: [Type]) (a :: Type) :: Type where
  ApiEvalType '[]      a = a
  ApiEvalType (p : ps) a = p -> ApiEvalType ps a


-- | Name of an API call
class (forall p a. Eq (api p a), Typeable api) => ApiName (api :: ApiDefinition) where
  apiName             :: api p a -> String
  showApiFromPat      :: api p a -> ArgPattern p -> String
  apiMetaAttributes   :: api p a -> [ApiMetaAttribute]
  apiNameUnder        :: String -> api p a -> String

  apiArgsAreValid     :: api p a -> Args p -> Maybe ErrorMsg

  default apiName :: (forall p a. Show (api p a)) => api p a -> String
  apiName = quietSnake . show
  {-# inline apiName #-}

  apiNameUnder _ = apiName
  {-# inline apiNameUnder #-}

  showApiFromPat = showApiFromPatDefault
  {-# inline showApiFromPat #-}

  apiMetaAttributes _ = []
  {-# inline apiMetaAttributes #-}

  apiArgsAreValid _ _ = Nothing


-- | Given API spec has a direct mapping to its haskell pure implementation
class HasHaskellDef (api :: ApiDefinition) where
  evalHaskell :: api p a -> Args p -> a

class HasForeignDef (api :: ApiDefinition) where
  evalForeign :: forall sig m p a. (HasForeign sig m, All Fuzzable p, Fuzzable a) => api p a -> Args p -> m a

applyArgs :: ApiEvalType p a -> Args p -> a
applyArgs a Nil         = a
applyArgs f (I p :* ps) = applyArgs (f p) ps
{-# inline applyArgs #-}

implE :: (HasForeign sig m) => ApiEvalType p (m a) -> Args p -> m a
implE = applyArgs
{-# inline implE #-}

implV :: ApiEvalType p (Maybe ErrorMsg) -> Args p -> Maybe ErrorMsg
implV = applyArgs
{-# inline implV #-}

showApiFromPatDefault :: ApiName api => api p1 a -> ArgPattern p2 -> String
showApiFromPatDefault f args = apiName f <> "(" <> showArgs args <> ")"
  where
    showArgs :: ArgPattern p -> [Char]
    showArgs Nil          = ""
    showArgs (K s :* Nil) = s
    showArgs (K s :* as)  = s <> ", " <> showArgs as
    {-# INLINE showArgs #-}

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

runForeign' :: (ApiError -> m b)
            -> (a1 -> m b)
            -> (ApiMetasState -> a2 -> ErrorC ApiError m a1)
            -> (Int -> a3 -> StateC ApiMetasState (ErrorC ApiError m) a2)
            -> ApiMetasState
            -> Int
            -> Labelled F FreshC (StateC ApiMetasState (ErrorC ApiError m)) a3
            -> m b
runForeign' fe fa fs ff s i x = runError fe fa $ runState fs s $ runFresh ff i $ runLabelled @F $ x

runForeign :: Monad m => (ApiError -> m b) -> (a -> m b) -> Labelled F FreshC (StateC ApiMetasState (ErrorC ApiError m)) a -> m b
runForeign fe fa = runForeign' fe fa (\s a -> return a) (\s a -> return a) emptyApiMetasState 0

isExternalPure :: ApiName api => api p a -> Bool
isExternalPure n = EXTERNAL_PURE `elem` apiMetaAttributes n

class (ApiName sub, ApiName sup) => ApiMember sub sup where
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

  showApiFromPat (ApiL f) = showApiFromPat f
  showApiFromPat (ApiR g) = showApiFromPat g

  apiMetaAttributes (ApiL f) = apiMetaAttributes f
  apiMetaAttributes (ApiR g) = apiMetaAttributes g

  apiNameUnder lang (ApiL f) = apiNameUnder lang f
  apiNameUnder lang (ApiR g) = apiNameUnder lang g

  apiArgsAreValid (ApiL f) a = apiArgsAreValid f a
  apiArgsAreValid (ApiR g) a = apiArgsAreValid g a

instance (HasHaskellDef f, HasHaskellDef g) => HasHaskellDef (f :$$: g) where
  evalHaskell (ApiL f) args = evalHaskell f args
  evalHaskell (ApiR g) args = evalHaskell g args

instance (HasForeignDef f, HasForeignDef g) => HasForeignDef (f :$$: g) where
  evalForeign (ApiL f) args = evalForeign f args
  evalForeign (ApiR g) args = evalForeign g args

type family ApiMembersF sub sup :: Constraint where
  ApiMembersF (f :$$: g) u = (ApiMembersF f u, ApiMembersF g u)
  ApiMembersF t          u = ApiMember t u

type ApiMembers sub sup = (ApiMembersF sub sup, ApiMembersC sub sup)

class (ApiName sub, ApiName sup) => ApiMembersC sub sup where
  injApis :: sub p a -> sup p a

instance {-# OVERLAPPABLE #-}
         ( ApiMember t u
         , ApiName t
         , ApiName u)
      => ApiMembersC t u where
  injApis = injApi
  {-# INLINE injApis #-}


instance {-# OVERLAPPABLE #-}
         ( ApiMembersC f u
         , ApiMembersC g u
         , ApiName f
         , ApiName g
         , ApiName u)
      => ApiMembersC (f :$$: g) u where
  injApis (ApiL f) = injApis f
  injApis (ApiR g) = injApis g
  {-# INLINE injApis #-}

class (ApiName api) => HaskellIOCall (api :: ApiDefinition) where
  readOut  :: api p a -> String -> Maybe a


-- Meta Attributes maintained during runtime

newtype LiftApiMeta api = LiftApiMeta { toApiMeta :: Meta api }

newtype ApiMetasState = ApiMetasState (TypeRepMap LiftApiMeta)

class ApiName api => HasApiMeta (api :: ApiDefinition)  where
  type Meta api :: Type
  initApiMeta :: Meta api

emptyApiMetasState :: ApiMetasState
emptyApiMetasState = ApiMetasState TM.empty

apiMeta' :: forall a. (Typeable a, HasApiMeta a) => ApiMetasState -> (ApiMetasState, Meta a)
apiMeta' s@(ApiMetasState ms) = case TM.lookup @a ms of
  Nothing              -> let i = initApiMeta @a in (ApiMetasState (TM.insert @a (LiftApiMeta i) ms), i)
  Just (LiftApiMeta m) -> (s, m)

insertMeta' :: forall a. (Typeable a, HasApiMeta a) => Meta a -> ApiMetasState -> ApiMetasState
insertMeta' m s@(ApiMetasState ms) = ApiMetasState (TM.insert @a (LiftApiMeta m) ms)

updateMeta' :: forall a. (Typeable a, HasApiMeta a) => (Meta a -> Meta a) -> ApiMetasState -> ApiMetasState
updateMeta' f s = insertMeta' @a (f m) s'
  where
    (s', m) = apiMeta' @a s

apiMeta :: forall a sig m. (Typeable a, HasApiMeta a, Has (State ApiMetasState) sig m) => m (Meta a)
apiMeta = state (apiMeta' @a)

getsMeta :: forall a b sig m. (Typeable a, HasApiMeta a, Has (State ApiMetasState) sig m) => (Meta a -> b) -> m b
getsMeta f = f <$> apiMeta @a

insertMeta :: forall a sig m. (Typeable a, HasApiMeta a, Has (State ApiMetasState) sig m) => Meta a -> m ()
insertMeta m = modify (insertMeta' @a m)

updateMeta :: forall a sig m. (Typeable a, HasApiMeta a, Has (State ApiMetasState) sig m) => (Meta a -> Meta a) -> m ()
updateMeta f = modify (updateMeta' @a f)



instance Show ApiError where
  show (ApiError api cause) = printf "Api Error: when calling %s: \n    %s" api cause
