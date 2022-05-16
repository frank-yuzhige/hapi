{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Test.HAPI.ApiTrace.TyConst where

class TyConst e d t | t e -> d where
  toConst :: t       -> e
  toType  :: proxy t -> d
