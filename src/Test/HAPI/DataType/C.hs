{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Test.HAPI.DataType.C where
import Test.HAPI.DataType (TyIso(..), TyConst(..))
import Foreign.C (CInt, CBool (..), CChar)
import Language.C (CExpr)
import Test.HAPI.ApiTrace.CodeGen.C.Util (cInt)

data C

instance TyIso C Int CInt where
  fromC = fromIntegral
  toC   = fromIntegral

instance TyIso C Bool CBool where
  fromC     = (/= 0)
  toC True  = CBool 1
  toC False = CBool 0

instance TyIso C Char CChar where


instance TyConst C CExpr CInt where
  toConst = cInt . fromIntegral
