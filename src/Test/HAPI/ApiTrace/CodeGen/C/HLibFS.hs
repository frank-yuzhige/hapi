
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Test.HAPI.ApiTrace.CodeGen.C.HLibFS where

import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.ApiTrace.CodeGen.C.Data (Entry2BlockC (..), entry2BlockDefault, dirAttrs2CExprs, pk2CVar)
import Test.HAPI.Constraint (CMembers, castC, productC)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen, TyConstC (..))
import Test.HAPI.ApiTrace.Core (ApiTraceEntry (..))
import Language.C.Syntax.AST (CBlockItem, CBinaryOp (..), CExpr)
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.PState (PKey(..))
import Test.HAPI.HLib.HLibFS (HLibFS(..))


instance Entry2BlockC HLibFS where
  -- TODO
