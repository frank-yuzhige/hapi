{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Test.HAPI.ApiTrace.CodeGen.C.Data where

import Test.HAPI.ApiTrace.Core (ApiTraceEntry(..), ApiTrace (..), trace2List)
import Language.C
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.PState ( PKey(getPKeyID, PKey) )
import Test.HAPI.Api (ApiName (..))
import Data.SOP (All, NP (..))
import Test.HAPI.Constraint (type (:>>>:), castC)
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.Args (DirectAttribute (..), DirAttributes)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen)
import Test.HAPI.ApiTrace.TyConst (TyConst(..))

entry2Block :: forall api c. (c :>>>: CCodeGen) => ApiTraceEntry api c -> CBlockItem
entry2Block (TraceCall (x :: PKey a) api args) = CBlockDecl $ decl
  ty
  (f $ cDeclr $ getPKeyID x)
  (Just $ api2CVar api # dirAttrs2CExprs @c args)
  where
    (ty, f) = toType @CExpr x \\ castC @CCodeGen (Dict @(c a))
entry2Block (TraceAssert p) = liftEToB $ cAssert (dirAttr2CExpr p)

entryFun :: forall api c.
          ( c :>>>: CCodeGen)
       => String            -- entryFunctionName
       -> ApiTrace api c    -- Trace
       -> CFunDef
entryFun fn trace = fun [intTy] fn [] body
  where
    body = CCompound [] blocks undefNode
    blocks = map entry2Block (trace2List trace)
          <> [CBlockStmt $ creturn $ cIntConst 0]

pk2CVar :: PKey a -> CExpr
pk2CVar = cVar . getPKeyID

api2CVar :: ApiName api => api p a -> CExpr
api2CVar a = cVar $ apiNameUnder "C" a

dirAttr2CExpr :: (Fuzzable a, CCodeGen a) => DirectAttribute a -> CExpr
dirAttr2CExpr (Value a) = toConst a
dirAttr2CExpr (Get   x) = pk2CVar x

dirAttrs2CExprs :: forall c p. (All Fuzzable p, All c p, c :>>>: CCodeGen) => DirAttributes p -> [CExpr]
dirAttrs2CExprs Nil = []
dirAttrs2CExprs ((a :: DirectAttribute a) :* as)
  = (dirAttr2CExpr a \\ castC @CCodeGen (Dict @(c a))) : dirAttrs2CExprs @c as

