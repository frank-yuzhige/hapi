{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.AASTG.Synth where
import Control.Algebra (Has, type (:+:), send)
import Test.HAPI.Effect.Api (Api, mkCall)
import Test.HAPI.Effect.QVS (QVS(QVS), attributes2QVSs, qvs2m)
import Control.Effect.State (State, modify)
import Test.HAPI.PState (PState, PStateSupports (record, forget))
import Test.HAPI.Effect.Property (PropertyA, shouldBe)
import Test.HAPI.AASTG.Core (AASTG (AASTG, getStart), Edge (Update, Forget, Assert, APICall, Redirect), endNode, NodeID, edgesFrom)
import Test.HAPI.Args (Attribute(Get))

import qualified Data.IntMap as IM
import Test.HAPI.Effect.Fuzzer (Fuzzer, EntropyFuzzer)
import Test.HAPI.Effect.Orchestration (Orchestration, nextInstruction)
import Test.HAPI.Effect.Orchestration.Labels (EntropySupply)
import Data.ByteString (ByteString)
import Control.Lens (element, (^?))
import Data.Serialize (Serialize(put), runPut)
import Test.HAPI.Effect.Eff ( send, debug, Alg )

-- | Synthesize fuzzer stubs
synthStub :: forall api sig c m. (Has (Fuzzer api c) sig m) => AASTG api c -> [m ()]
synthStub (AASTG start edges _) = synth start
  where
    synth i = case edges IM.!? i of
      Nothing -> [return ()]
      Just [] -> [return ()]
      Just es -> concat [(synthOneStep edge >>) <$> synth (endNode edge) | edge <- es]

synthOneStep :: forall api sig c m. (Has (Fuzzer api c) sig m) => Edge api c -> m ()
synthOneStep (Update s e k a) = do
  v <- send (QVS @c a)
  modify @PState (record k v)
synthOneStep (Forget s e k) = do
  modify @PState (forget k)
synthOneStep (Assert s e x y) = do
  x' <- send (QVS @c (Get x))
  y' <- send (QVS @c (Get y))
  x' `shouldBe` y'
synthOneStep (APICall s e mx api args) = do
  -- 1. Resolve Attributes (Into QVS)
  args <- qvs2m @c (attributes2QVSs args)
  -- 2. Make APICall using qvs
  r <- mkCall api args
  -- 3. Store return value in state
  case mx of
    Nothing -> return ()
    Just k  -> modify @PState (record k r)
synthOneStep (Redirect s e) = return ()

-- | Entropy
type EntropyWord = Int
type Entropy     = [EntropyWord]

encodeEntropy :: Entropy -> ByteString
encodeEntropy e = runPut $ mapM_ put e

lookupEdgeFromEntropy :: NodeID -> AASTG api c -> EntropyWord -> Maybe (Edge api c)
lookupEdgeFromEntropy n aastg e = edgesFrom n aastg ^? element e

data EntropyStubResult = EntropyStubResult {

}

synthEntropyStub :: forall api sig c m.
                  ( Has (EntropyFuzzer api c) sig m
                  , Alg sig m )
                 => AASTG api c -> m ()
synthEntropyStub aastg = go (getStart aastg)
  where
    go i = do
      w <- nextInstruction @EntropySupply @EntropyWord
      case lookupEdgeFromEntropy i aastg w of
        Nothing -> do
          debug "[HAPI]: Entropy hits an invalid path."
          return ()
        Just e  -> do
          synthOneStep e
          go (endNode e)
