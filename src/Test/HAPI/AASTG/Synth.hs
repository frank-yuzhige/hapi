{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.Synth where
import Control.Algebra (Has, type (:+:), send)
import Test.HAPI.Effect.Api (Api, mkCall)
import Test.HAPI.Effect.QVS (QVS(QVS), attributes2QVSs, qvs2m, qvs2Direct)
import Control.Effect.State (State, modify)
import Test.HAPI.PState (PState, PStateSupports (record, forget))
import Test.HAPI.Effect.Property (PropertyA, shouldBe)
import Test.HAPI.AASTG.Core (AASTG (AASTG, getStart), Edge (Update, Forget, Assert, APICall, Redirect), endNode, NodeID, edgesFrom)
import Test.HAPI.Args (Attribute(..), getVar)

import qualified Data.IntMap as IM
import Test.HAPI.Effect.Fuzzer (Fuzzer, EntropyFuzzer, EntropyTracer)
import Test.HAPI.Effect.Orchestration (Orchestration, nextInstruction)
import Test.HAPI.Effect.Orchestration.Labels (EntropySupply)
import Data.ByteString (ByteString)
import Control.Lens (element, (^?))
import Data.Serialize (Serialize(put), runPut)
import Test.HAPI.Effect.Eff ( send, debug, Alg )
import Test.HAPI.Effect.Entropy (getEntropy)
import Test.HAPI.AASTG.Effect.Trav (TravHandler (..), TravEvent (..), onEvent)
import Control.Effect.Writer (tell)
import Test.HAPI.ApiTrace (ApiTraceEntry(TraceCall), traceCall)

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
  x' <- send (QVS @c (getVar x))
  y' <- send (QVS @c (getVar y))
  x' `shouldBe` y'
synthOneStep (APICall s e x api args) = do
  -- 1. Resolve Attributes (Into QVS)
  args <- qvs2m @c (attributes2QVSs args)
  -- 2. Make APICall using qvs
  r <- mkCall api args
  -- 3. Store return value in state
  modify @PState (record x r)
synthOneStep (Redirect s e) = return ()

traceOneStep :: forall api sig c m. (Has (EntropyTracer api c) sig m) => Edge api c -> m ()
traceOneStep (Update s e k a) = do
  v <- send (QVS @c a)
  modify @PState (record k v)
traceOneStep (Forget s e k) = do
  modify @PState (forget k)
traceOneStep (Assert s e x y) = do
  x' <- send (QVS @c (getVar x))
  y' <- send (QVS @c (getVar y))
  x' `shouldBe` y'
traceOneStep (APICall s e x api args) = do
  args <- qvs2Direct @c (attributes2QVSs args)
  tell (traceCall x api args)
traceOneStep (Redirect s e) = do
  return ()

execEntropyFuzzerHandler :: forall api c sig m. (Has (Fuzzer api c) sig m) => TravHandler api c m
execEntropyFuzzerHandler = TravHandler $ \case
  OnEdge e -> synthOneStep e
  OnNode n -> return ()

execEntropyTraceHandler :: forall api c sig m. (Has (EntropyTracer api c) sig m) => TravHandler api c m
execEntropyTraceHandler = TravHandler $ \case
   OnEdge e -> traceOneStep e
   OnNode n -> return ()

-- | Entropy
type EntropyWord = Int
type Entropy     = [EntropyWord]

encodeEntropy :: Entropy -> ByteString
encodeEntropy e = runPut $ mapM_ put e

lookupEdgeFromEntropy :: NodeID -> AASTG api c -> EntropyWord -> Maybe (Edge api c)
lookupEdgeFromEntropy n aastg e = edgesFrom n aastg ^? element e

data EntropyStubResult = EntropyStubResult {

}

synthEntropyStub :: forall api c sig m.
                  ( Has (EntropyFuzzer api c) sig m
                  , Alg sig m )
                 => AASTG api c -> m ()
synthEntropyStub aastg = go (getStart aastg)
  where
    go i = do
      let choice = edgesFrom i aastg
      if null choice then return () else do
        w <- getEntropy (length choice)
        case lookupEdgeFromEntropy i aastg w of
          Nothing -> do
            debug "[HAPI]: Entropy hits an invalid path."
            return ()
          Just e  -> do
            onEvent (OnEdge e)
            go (endNode e)
