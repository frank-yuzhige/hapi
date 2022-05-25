
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Test.HAPI.ApiTrace.CodeGen.C.HLibCString where

import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.ApiTrace.CodeGen.C.Data (Entry2BlockC (..), entry2BlockDefault, dirAttrs2CExprs, pk2CVar)
import Test.HAPI.Constraint (CMembers, castC, productC)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen, TyConstC (..))
import Test.HAPI.ApiTrace.Core (ApiTraceEntry (..))
import Language.C.Syntax.AST (CBlockItem, CBinaryOp (..), CExpr)
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.PState (PKey(..))
import Test.HAPI.HLib.HLibCString (HLibCString (..))


instance Entry2BlockC HLibCString where
  entry2Block :: forall c. (CMembers CCodeGen c) => ApiTraceEntry HLibCString c -> CBlockItem
  entry2Block a@TraceAssert {} = entry2BlockDefault a
  entry2Block a@(TraceCall (x :: PKey a) f args) = case f of
    PeekCString    -> liftEToB undefined
    PeekCStringLen -> liftEToB undefined
    NewCString     -> liftEToB $ pk2CVar x <-- let [a] = aExprs in a
    where
      aExprs = dirAttrs2CExprs @c args
      (ty, _) = toCType x \\ mapDict (productC @CCodeGen) (Dict @(c a))
