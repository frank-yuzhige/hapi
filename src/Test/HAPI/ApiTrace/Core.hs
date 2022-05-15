{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.HAPI.ApiTrace.Core where
import Test.HAPI.Api (ApiDefinition, ApiName (..), ValidApiDef)
import Data.SOP (All, NP)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.Args (Args, Attributes, attrs2Pat, DirectAttribute, dirAttrs2Pat)
import Data.DList (DList)
import qualified Data.DList as DL
import Test.HAPI.PState (PKey)

data ApiTraceEntry (api :: ApiDefinition) where
  TraceCall :: (ValidApiDef api, All Fuzzable p) => PKey a -> api p a -> NP DirectAttribute p -> ApiTraceEntry api

instance ApiName api => Show (ApiTraceEntry api) where
  show (TraceCall k api args) = show k <> "=" <> showApiFromPat api (dirAttrs2Pat args)

newtype ApiTrace (api :: ApiDefinition) = ApiTrace { apiTrace2List :: DList (ApiTraceEntry api) }
  deriving (Semigroup, Monoid)

apiTrace :: ApiTraceEntry api -> ApiTrace api
apiTrace = ApiTrace . DL.singleton

traceCall :: (ValidApiDef api, All Fuzzable p) =>PKey a ->  api p a -> NP DirectAttribute p -> ApiTrace api
traceCall k api args = apiTrace $ TraceCall k api args

instance Show (ApiTraceEntry api) => Show (ApiTrace api) where
  show (ApiTrace xs) = "ApiTrace " <> show xs
