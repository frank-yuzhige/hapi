{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

module Test.HAPI.AASTG.Synth where
import Control.Algebra (Has, type (:+:), send)
import Test.HAPI.Effect.Api (Api, mkCall)
import Test.HAPI.Effect.QVS (QVS(..), attributes2QVSs, qvs2m, qvs2Direct, qvs2Directs, mkQVS)
import Control.Effect.State (State, modify, get)
import Test.HAPI.PState (PState, PStateSupports (record, forget), PKey (PKey))
import Test.HAPI.Effect.Property (PropertyA (..))
import Test.HAPI.AASTG.Core (AASTG (AASTG, getStart), Edge (..), endNode, NodeID, edgesFrom)
import Test.HAPI.Args (Attribute (..), evalDirect')

import qualified Data.IntMap as IM
import Test.HAPI.Effect.Fuzzer (Fuzzer, EntropyFuzzer, EntropyTracer)
import Test.HAPI.Effect.Orchestration.Labels (EntropySupply)
import Data.ByteString (ByteString)
import Control.Lens (element, (^?))
import Data.Serialize (Serialize(put), runPut)
import Test.HAPI.Effect.Eff ( send, debug, Alg )
import Test.HAPI.Effect.Entropy (getEntropy, EntropySupplier)
import Test.HAPI.AASTG.Effect.Trav (TravHandler (..), TravEvent (..), onEvent, TravEventResult (..), Trav)
import Control.Effect.Writer (tell)
import Test.HAPI.ApiTrace (ApiTraceEntry(TraceCall), traceCall, traceAssert)
import Data.Constraint ((\\), Dict (..))
import Text.Printf (printf)
import Data.Data (Typeable)
import Control.Monad (when)
import Test.HAPI.Effect.VarUpdate (VarUpdate(VarUpdate))

-- | Synthesize fuzzer stubs
synthStub :: forall api c sig m. (Has (Fuzzer api c) sig m, Typeable c) => AASTG api c -> [m ()]
synthStub (AASTG start edges _) = synth start
  where
    synth i = case edges IM.!? i of
      Nothing -> [return ()]
      Just [] -> [return ()]
      Just es -> concat [(synthOneStep edge >>) <$> synth (endNode edge) | edge <- es]

synthOneStep :: forall api c sig m. (Has (Fuzzer api c) sig m, Typeable c) => Edge api c -> m TravEventResult
synthOneStep (Update s e k a) = do
  v <- qvs2Direct $ mkQVS @c a
  send (VarUpdate @_ @c @api k v)
  return NO_RESULT
synthOneStep (ContIf s e p) = do
  continue <- send (ChecksA p)
  return $ if continue then NO_RESULT else HALT
synthOneStep (Assert s e p) = do
  send (AssertA p)
  return NO_RESULT
synthOneStep (APICall s e x api args) = do
  -- 1. Resolve Attributes (Into QVS)
  attrs <- qvs2Directs @c (attributes2QVSs args)
  -- 2. Make APICall using qvs
  mkCall @c x api attrs
  -- 3. Store return value in state
  return NO_RESULT
synthOneStep (Redirect s e) = return NO_RESULT

execEntropyFuzzerHandler :: forall api c sig m. (Has (Fuzzer api c) sig m, Typeable c) => TravHandler api c m
execEntropyFuzzerHandler = TravHandler $ \case
  OnEdge e -> synthOneStep e
  OnNode n -> return NO_RESULT

-- | Entropy
type EntropyWord = Int
type Entropy     = [EntropyWord]

encodeEntropy :: Entropy -> ByteString
encodeEntropy e = runPut $ mapM_ put e

lookupEdgeFromEntropy :: NodeID -> AASTG api c -> EntropyWord -> Maybe (Edge api c)
lookupEdgeFromEntropy n aastg e = edgesFrom n aastg ^? element e


data EntropyStubResult
  = TERMINATE_SUCCESSFULLY
  | ENTROPY_EXHAUST
  | ENTROPY_HIT_INVALID_PATH
  deriving (Eq, Ord, Show, Enum, Bounded)

synthEntropyStub :: forall api c sig m.
                  ( Has (Trav api c :+: EntropySupplier) sig m
                  , Alg sig m )
                 => AASTG api c -> m EntropyStubResult
synthEntropyStub aastg = go (getStart aastg)
  where
    go i = do
      let choice = edgesFrom i aastg
      if null choice then return TERMINATE_SUCCESSFULLY else do
        mw <- getEntropy (length choice)
        case mw of
          Nothing -> do
            debug "[HAPI]: Entropy Exhausted."
            return ENTROPY_EXHAUST
          Just w -> case lookupEdgeFromEntropy i aastg w of
            Nothing -> do
              debug "[HAPI]: Entropy hits an invalid path."
              return ENTROPY_HIT_INVALID_PATH
            Just e  -> do
              r <- onEvent (OnEdge e)
              if r == HALT
                then return TERMINATE_SUCCESSFULLY
                else go (endNode e)
