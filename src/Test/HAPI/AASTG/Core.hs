{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.AASTG.Core where
import Test.HAPI.QVS (QVS (QVS), Attribute, LiftArgs, attributes2QVSs, qvs2m)
import GHC.TypeNats (Nat)
import Data.Kind (Type)
import Data.HList (HList (HCons, HNil), hMap)
import Test.HAPI.Lib (ArithApiA(AddA))
import Test.HAPI.Api (ApiDefinition, Api, mkCall)
import Control.Effect.Sum (Member)
import Control.Algebra (Has, Algebra, type (:+:))
import Test.HAPI.Args (Args)
import Test.HAPI.PState (PKey (PKey), PState (PState), PStateSupports (record))
import Test.HAPI.Common (Fuzzable)
import Control.Effect.State (State, modify)
import Data.SOP (All)

-- Abstract API state transition graph

type PStateID = Nat


data Edge sig c where
  APICall :: (Member (Api api) sig, Fuzzable a, All c p)
          => Int   -- From
          -> Int   -- To
          -> api p a               -- API call (constructor)
          -> LiftArgs Attribute p
          -> Edge sig c

start :: Edge api c -> Int
start (APICall s _ _ _) = s

end :: Edge api c -> Int
end (APICall _ e _ _) = e

data AASTG sig c = AASTG {
  getStart :: Int,
  getEdges :: [Edge sig c]
}

edgesFrom :: Int -> AASTG api c -> [Edge api c]
edgesFrom i (AASTG _ es) = filter ((== i) . start) es

edgesTo :: Int -> AASTG api c -> [Edge api c]
edgesTo i (AASTG _ es) = filter ((== i) . end) es

synthStub :: forall apis sig c m. (Has (apis :+: QVS c :+: State PState) sig m) => AASTG sig c -> [m ()]
synthStub aastg@(AASTG start edges) = synth start
  where
    synth i = return ()
            : concat [(synthOneStep e >>) <$> synth (end e) | e <- edgesFrom i aastg]
    synthOneStep :: (Has (apis :+: QVS c :+: State PState) sig m) => Edge sig c -> m ()
    synthOneStep (APICall s e (api :: api p a) (args :: LiftArgs Attribute p)) = do
      -- TODO
      -- 1. Resolve Attributes (Into QVS)
      let qvss = attributes2QVSs @c args
      args <- qvs2m @c @sig @m qvss
      -- 2. Make APICall using qvs
      r <- mkCall api args
      -- 3. Check if return value satisfies condition

      -- 4. Store return value in state
      modify @PState (record (PKey 42) r)
      return ()
