{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
module Test.HAPI.ApiTrace.CodeGen.C.DataType where
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Test.HAPI.DataType.C (C)
import Language.C (CExpr, CDeclSpec, CDerivedDeclr, CDeclr)
import Test.HAPI.ApiTrace.CodeGen.C.Util

type CCodeGen = TyConst CExpr (CDeclSpec, CDeclr -> CDeclr)

instance TyConst CExpr (CDeclSpec, CDeclr -> CDeclr) Int where
  toConst  = cIntConst . fromIntegral
  toType _ = (intTy, id)

instance TyConst CExpr (CDeclSpec, CDeclr -> CDeclr) Bool where
  toConst  = cBoolConst
  toType _ = (boolTy, id)

instance TyConst CExpr (CDeclSpec, CDeclr -> CDeclr) Char where
  toConst  = cCharConst
  toType _ = (charTy, id)


instance TyConst CExpr (CDeclSpec, CDeclr -> CDeclr) String where
  toConst  = cStrConst
  toType _ = (charTy, ptr)
