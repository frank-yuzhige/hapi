{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.HAPI.ApiTrace.Core where
import Test.HAPI.Api (ApiDefinition, ApiName (..), ValidApiDef)
import Data.SOP (All, NP)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.Args (Args, Attributes, attrs2Pat, DirectAttribute, dirAttrs2Pat, DirAttributes)
import Data.DList (DList)
import qualified Data.DList as DL
import Test.HAPI.PState (PKey)
import Data.Constraint (Constraint)
import Data.Kind (Type)
import Data.Data (Typeable)

data ApiTraceEntry (api :: ApiDefinition) (c :: Type -> Constraint) where
  TraceCall   :: (ApiName api, All Fuzzable p, All c p, c a, Typeable a)
              => PKey a -> api p a -> DirAttributes c p -> ApiTraceEntry api c
  TraceAssert :: (c Bool)
              => DirectAttribute c Bool -> ApiTraceEntry api c
  TraceContIf :: (c Bool)
              => DirectAttribute c Bool -> ApiTraceEntry api c
  TraceDirect :: (Fuzzable a, c a)
              => PKey a -> DirectAttribute c a -> ApiTraceEntry api c

instance ApiName api => Show (ApiTraceEntry api c) where
  show (TraceCall   k api args) = show k <> "=" <> showApiFromPat api (dirAttrs2Pat args)
  show (TraceAssert p)          = "assert " <> show p
  show (TraceContIf p)          = "contif " <> show p
  show (TraceDirect k d)        = "direct " <> show k <> show d

newtype ApiTrace (api :: ApiDefinition) (c :: Type -> Constraint) = ApiTrace { apiTrace2List :: DList (ApiTraceEntry api c) }
  deriving (Semigroup, Monoid)

apiTrace :: ApiTraceEntry api c -> ApiTrace api c
apiTrace = ApiTrace . DL.singleton

traceCall :: forall api c p a.
           ( ApiName api
           , All Fuzzable p
           , All c p
           , c a
           , Typeable a)
          => PKey a -> api p a -> DirAttributes c p -> ApiTrace api c
traceCall k api args = apiTrace $ TraceCall k api args

traceAssert :: forall api c. (c Bool) => DirectAttribute c Bool -> ApiTrace api c
traceAssert p = apiTrace $ TraceAssert @c @api p

traceContIf :: forall api c. (c Bool) => DirectAttribute c Bool -> ApiTrace api c
traceContIf p = apiTrace $ TraceContIf @c @api p

traceDirect :: forall api c a. (Fuzzable a, c a)
            => PKey a -> DirectAttribute c a -> ApiTrace api c
traceDirect p d = apiTrace $ TraceDirect @a @c @api p d

trace2List :: ApiTrace api c -> [ApiTraceEntry api c]
trace2List (ApiTrace dl) = DL.toList dl

instance Show (ApiTraceEntry api c) => Show (ApiTrace api c) where
  show (ApiTrace xs) = "ApiTrace " <> show xs
