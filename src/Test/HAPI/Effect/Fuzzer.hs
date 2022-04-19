{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

module Test.HAPI.Effect.Fuzzer where

import Control.Algebra
  ( Algebra(alg), type (:+:)(L, R), send, Has )
import Test.HAPI.Effect.Api (Api)
import Test.HAPI.Effect.QVS (QVS)
import Control.Effect.State (State)
import Test.HAPI.PState (PState)
import Test.HAPI.Effect.Property (PropertyA)

-- | Type Synonym of a fuzzer for an API set.
type Fuzzer api c = (Api api :+: QVS c :+: State PState :+: PropertyA)
