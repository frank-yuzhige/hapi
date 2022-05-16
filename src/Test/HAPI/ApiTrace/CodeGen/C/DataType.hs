{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
module Test.HAPI.ApiTrace.CodeGen.C.DataType where
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Test.HAPI.DataType.C (C)
import Language.C (CExpr)
import Test.HAPI.ApiTrace.CodeGen.C.Util

type CCodeGen = TyConst CExpr

instance TyConst CExpr Int where
  toConst = cIntConst . fromIntegral

instance TyConst CExpr Bool where
  toConst = cBoolConst

instance TyConst CExpr Char where
  toConst = cCharConst

instance TyConst CExpr String where
  toConst = cStrConst
