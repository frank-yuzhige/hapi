{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Test.HAPI.ApiTrace.TyConst where
import Test.HAPI.DataType (TyIso)

class TyConst e t where
  toConst :: t -> e
