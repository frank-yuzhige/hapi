{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
module Test.HAPI.ApiTrace.CodeGen.C.Data where

import Test.HAPI.ApiTrace.Core (ApiTraceEntry(..))
import Language.C
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.PState ( PKey(getPKeyID) )
import Test.HAPI.Api (ApiName (apiName))
import Test.HAPI (DirAttributes, Fuzzable, NP (..), DirectAttribute (..), TyIso (fromC))
import Data.SOP (All)

entry2Block :: ApiTraceEntry api -> CBlockItem
entry2Block (TraceCall x api args) = liftEToB $ pk2CVar x <-- (api2CVar api # dirAttrs2CExprs args)

pk2CVar :: PKey a -> CExpr
pk2CVar = cVar . getPKeyID

api2CVar :: ApiName api => api p a -> CExpr
api2CVar = cVar . apiName

dirAttr2CExpr :: Fuzzable a => DirectAttribute a -> CExpr
dirAttr2CExpr (Value a) = undefined
dirAttr2CExpr (Get   x) = pk2CVar x

dirAttrs2CExprs :: All Fuzzable p => DirAttributes p -> [CExpr]
dirAttrs2CExprs Nil       = []
dirAttrs2CExprs (a :* as) = dirAttr2CExpr a : dirAttrs2CExprs as

