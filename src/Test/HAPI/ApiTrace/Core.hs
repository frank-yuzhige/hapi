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
import Test.HAPI.Args (Args, Attributes, attrs2Pat, DirectAttribute, dirAttrs2Pat)
import Data.DList (DList)
import qualified Data.DList as DL
import Test.HAPI.PState (PKey)
import Data.Constraint (Constraint)
import Data.Kind (Type)

data ApiTraceEntry (api :: ApiDefinition) (c :: Type -> Constraint) where
  TraceCall   :: (ApiName api, All Fuzzable p, All c p, c a)
              => PKey a -> api p a -> NP DirectAttribute p -> ApiTraceEntry api c
  TraceAssert :: (c Bool)
              => DirectAttribute Bool -> ApiTraceEntry api c

instance ApiName api => Show (ApiTraceEntry api c) where
  show (TraceCall   k api args) = show k <> "=" <> showApiFromPat api (dirAttrs2Pat args)
  show (TraceAssert p)          = "assert " <> show p

newtype ApiTrace (api :: ApiDefinition) (c :: Type -> Constraint) = ApiTrace { apiTrace2List :: DList (ApiTraceEntry api c) }
  deriving (Semigroup, Monoid)

apiTrace :: ApiTraceEntry api c -> ApiTrace api c
apiTrace = ApiTrace . DL.singleton

traceCall :: forall api c p a.
           ( ApiName api
           , All Fuzzable p
           , All c p
           , c a)
          => PKey a -> api p a -> NP DirectAttribute p -> ApiTrace api c
traceCall k api args = apiTrace $ TraceCall k api args

traceAssert :: forall api c.
             (c Bool)
            => DirectAttribute Bool -> ApiTrace api c
traceAssert p = apiTrace $ TraceAssert @c @api p

trace2List :: ApiTrace api c -> [ApiTraceEntry api c]
trace2List (ApiTrace dl) = DL.toList dl

instance Show (ApiTraceEntry api c) => Show (ApiTrace api c) where
  show (ApiTrace xs) = "ApiTrace " <> show xs
