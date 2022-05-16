{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Test.HAPI.ApiTrace.CodeGen.C.Data where

import Test.HAPI.ApiTrace.Core (ApiTraceEntry(..))
import Language.C
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.PState ( PKey(getPKeyID) )
import Test.HAPI.Api (ApiName (apiName))
import Test.HAPI (DirAttributes, Fuzzable, NP (..), DirectAttribute (..))
import Data.SOP (All)
import Test.HAPI.Constraint (type (:>>>:), castC)
import Test.HAPI.ApiTrace.TyConst (TyConst (..))
import Data.Constraint ((\\), Dict (..), mapDict)

entry2Block :: forall api c. (c :>>>: TyConst CExpr) => ApiTraceEntry api c -> CBlockItem
entry2Block (TraceCall x api args) = liftEToB $ pk2CVar x <-- (api2CVar api # dirAttrs2CExprs @c args)

pk2CVar :: PKey a -> CExpr
pk2CVar = cVar . getPKeyID

api2CVar :: ApiName api => api p a -> CExpr
api2CVar = cVar . apiName

dirAttr2CExpr :: (Fuzzable a, TyConst CExpr a) => DirectAttribute a -> CExpr
dirAttr2CExpr (Value a) = toConst a
dirAttr2CExpr (Get   x) = pk2CVar x

dirAttrs2CExprs :: forall c p. (All Fuzzable p, All c p, c :>>>: TyConst CExpr) => DirAttributes p -> [CExpr]
dirAttrs2CExprs Nil = []
dirAttrs2CExprs ((a :: DirectAttribute a) :* as)
  = (dirAttr2CExpr a \\ castC @(TyConst CExpr) (Dict @(c a))) : dirAttrs2CExprs @c as

