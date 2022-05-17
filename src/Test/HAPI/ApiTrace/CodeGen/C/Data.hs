{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}

module Test.HAPI.ApiTrace.CodeGen.C.Data where

import Test.HAPI.ApiTrace.Core (ApiTraceEntry(..), ApiTrace (..), trace2List)
import Language.C
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.PState ( PKey(getPKeyID, PKey), emptyPKeySet, addPKey2Set, PKeySetEntry (..), PKeySet )
import Test.HAPI.Api (ApiName (..))
import Data.SOP (All, NP (..))
import Test.HAPI.Constraint (type (:>>>:), castC, CMembers, productC)
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.Args (DirectAttribute (..), DirAttributes)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen)
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Data.List (nub)
import qualified Test.HAPI.Util.TypeRepMap as TM
import qualified Data.Set as S
import Data.Data (Typeable)

entry2Block :: forall api c. (CMembers CCodeGen c) => ApiTraceEntry api c -> CBlockItem
entry2Block (TraceCall (x :: PKey a) api args) = liftEToB $ pk2CVar x <-- (api2CVar api # dirAttrs2CExprs @c args)
  where
    (ty, f) = toType @CExpr x \\ mapDict (productC @CCodeGen) (Dict @(c a))
entry2Block (TraceAssert p) = liftEToB $ cAssert (dirAttr2CExpr p)

traceDecls :: forall api c. (CMembers CCodeGen c) => [ApiTraceEntry api c] -> [CBlockItem]
traceDecls xs = concat $ TM.toListWith (\(PKeySetEntry s) -> [makeDecl k \\ mapDict (productC @CCodeGen) d | (k, d) <- S.toList s]) $ collectVar xs
  where
    collectVar :: [ApiTraceEntry api c] -> PKeySet c
    collectVar [] = emptyPKeySet
    collectVar (TraceCall (x :: PKey a) _ _ : xs) = addPKey2Set x \\ castC @Typeable (Dict @(c a)) $ collectVar xs
      -- where
      --   (ty, f) = toType @CExpr x \\ castC @CCodeGen (Dict @(c a))
    collectVar (_                           : xs) = collectVar xs

    makeDecl :: (CCodeGen a) => PKey a -> CBlockItem
    makeDecl (x :: PKey a) = CBlockDecl $ decl ty (f $ cDeclr $ getPKeyID x) Nothing
      where
        (ty, f) = toType @CExpr x


entryFun :: forall api c.
          (CMembers CCodeGen c)
       => String            -- entryFunctionName
       -> ApiTrace api c    -- Trace
       -> CFunDef
entryFun fn trace = fun [intTy] fn [] body
  where
    body = CCompound [] blocks undefNode
    blocks = traceDecls (trace2List trace)
          <> map entry2Block (trace2List trace)
          <> [CBlockStmt $ creturn $ cIntConst 0]

pk2CVar :: PKey a -> CExpr
pk2CVar = cVar . getPKeyID

api2CVar :: ApiName api => api p a -> CExpr
api2CVar a = cVar $ apiNameUnder "C" a

dirAttr2CExpr :: (Fuzzable a, CCodeGen a) => DirectAttribute a -> CExpr
dirAttr2CExpr (Value a) = toConst a
dirAttr2CExpr (Get   x) = pk2CVar x

dirAttrs2CExprs :: forall c p. (All Fuzzable p, All c p, CMembers CCodeGen c) => DirAttributes p -> [CExpr]
dirAttrs2CExprs Nil = []
dirAttrs2CExprs ((a :: DirectAttribute a) :* as)
  = (dirAttr2CExpr a \\ mapDict (productC @CCodeGen) (Dict @(c a))) : dirAttrs2CExprs @c as

