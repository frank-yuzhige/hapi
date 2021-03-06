{-# LANGUAGE TypeOperators #-}

module Test.HAPI.Effect.Fuzzer where

import Control.Algebra
  ( Algebra(alg), type (:+:)(L, R), send, Has )
import Test.HAPI.Effect.Api (Api)
import Test.HAPI.Effect.EVS (EVS)
import Control.Effect.State (State)
import Test.HAPI.PState (PState)
import Test.HAPI.Effect.Property (PropertyA)
import Test.HAPI.Effect.Orchestration (Orchestration)
import Test.HAPI.Effect.Orchestration.Labels (EntropySupply)
import Test.HAPI.Effect.Entropy (EntropySupplier)
import Test.HAPI.AASTG.Effect.Trav (Trav)
import Test.HAPI.ApiTrace.Core ( ApiTrace )
import Control.Effect.Writer (Writer)
import Test.HAPI.Effect.VarUpdate (VarUpdate)

-- | Type Synonym of a fuzzer for an API set.
type Fuzzer api c = (Api api c :+: EVS c :+: State PState :+: PropertyA c :+: VarUpdate api c)

type EntropyFuzzer api c = (Fuzzer api c :+: EntropySupplier :+: Trav api c)

type EntropyTracer api c = (EVS c :+: State PState :+: PropertyA c :+: EntropySupplier :+: Writer (ApiTrace api c))
