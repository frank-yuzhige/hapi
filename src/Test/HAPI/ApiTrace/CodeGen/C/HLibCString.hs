
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Test.HAPI.ApiTrace.CodeGen.C.HLibCString where

import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.ApiTrace.CodeGen.C.Data (Entry2BlockC (..), call2BlockDefault, dirAttrs2CExprs, pk2CVar)
import Test.HAPI.Constraint (CMembers, castC, productC)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen, TyConstC (..))
import Test.HAPI.ApiTrace.Core (ApiTraceEntry (..))
import Language.C.Syntax.AST (CBlockItem, CBinaryOp (..), CExpr)
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.PState (PKey(..))
import Test.HAPI.HLib.HLibCString (HLibCString (..))
import Data.SOP (All)
import Test.HAPI.Common (Fuzzable)
import Data.Data (Typeable)
import Test.HAPI.Args (DirAttributes)


instance Entry2BlockC HLibCString where
  call2Block :: forall c p a. (CMembers CCodeGen c, All Fuzzable p, Typeable a, All c p, c a)
             => PKey a -> HLibCString p a -> DirAttributes c p -> [CBlockItem]
  call2Block x f args = case f of
    PeekCString    -> [liftEToB undefined]
    PeekCStringLen -> [liftEToB undefined]
    NewCString     -> [liftEToB $ pk2CVar x <-- let [a] = aExprs in a]
    StringLen      -> [liftEToB $ pk2CVar x <-- let [a] = aExprs in cStrlen a]
    where
      aExprs = dirAttrs2CExprs @c args
      (ty, _) = toCType x \\ mapDict (productC @CCodeGen) (Dict @(c a))
