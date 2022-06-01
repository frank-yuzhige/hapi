
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Test.HAPI.ApiTrace.CodeGen.C.HLibFS where

import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.ApiTrace.CodeGen.C.Data (Entry2BlockC (..), dirAttrs2CExprs, pk2CVar)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen, TyConstC (..))
import Test.HAPI.ApiTrace.Core (ApiTraceEntry (..))
import Language.C.Syntax.AST (CBlockItem, CBinaryOp (..), CExpr)
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.PState (PKey(..))
import Test.HAPI.HLib.HLibFS (HLibFS(..))
import Language.C.Syntax
import Language.C (undefNode)


instance Entry2BlockC HLibFS where
  call2Block x f args = case f of
    NewFile ->
      [ liftEToB $ pk2CVar x    <-- cStrConst filename
      , liftEToB $ cVar varname <-- cFOpen (pk2CVar x) (cStrConst "w+") -- FILE *fp = fopen(filepath, "w+");
      , CBlockStmt $ CIf (cVar filename) writeNClose Nothing undefNode
      ]
      where
        [content] = aExprs
        filename = "hapi_file__" <> show x
        varname  = filename
        writeNClose = block
          [ liftEToB $ cFPuts content (cVar filename)
          , liftEToB $ cFClose (cVar filename)
          ]
    where
      aExprs = dirAttrs2CExprs args
  extraDecls x f args = case f of
    NewFile -> [decl fileTy (ptr $ cDeclr ("hapi_file__" <> show x)) Nothing]


