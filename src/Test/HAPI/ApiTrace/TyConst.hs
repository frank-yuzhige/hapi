{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
module Test.HAPI.ApiTrace.TyConst where
import Test.HAPI.DataType (TyIso)

class TyConst e d t | t e -> d where
  toConst :: t       -> e
  toType  :: proxy t -> d
