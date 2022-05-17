{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}

module Test.HAPI.ApiTrace.CodeGen.C.DataType where
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Language.C (CExpr, CDeclSpec, CDerivedDeclr, CDeclr)
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Data.Data (Typeable)
import Test.HAPI.Constraint (type (:<>:))

type CCodeGen = TyConst CExpr (CDeclSpec, CDeclr -> CDeclr) :<>: Typeable

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
