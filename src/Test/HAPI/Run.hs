{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.HAPI.Run where
import Test.HAPI.AASTG.Core (AASTG(AASTG))
import Control.Monad.IO.Class (MonadIO, liftIO)
import Test.QuickCheck (Arbitrary)
import Test.HAPI.Effect.Property
    ( PropertyA, PropertyError, runProperty )
import Test.HAPI.Api (runForeign, HasForeignDef, ApiName, ValidApiDef)
import qualified Test.HAPI.PState as PS
import Test.HAPI.Effect.Eff (debug, runEnvIO, Algebra)
import Test.HAPI.AASTG.Synth (synthStub, synthEntropyStub, execEntropyFuzzerHandler, execEntropyTraceHandler)
import Test.HAPI.AASTG.Analysis.Path (outPaths)
import Control.Monad (forM_, void)
import Test.HAPI.Effect.Gen (runGenIO)
import Control.Carrier.Error.Church (runError)
import Control.Carrier.Writer.Church (runWriter)
import Test.HAPI.Effect.Api (runApiFFI, runApiTrace)
import Control.Carrier.State.Church (runState)
import Test.HAPI.Effect.QVS (runQVSFuzzArbitraryAC, QVSFromOrchestrationAC (runQVSFromOrchestrationAC))
import Data.ByteString (ByteString)
import Test.HAPI.Effect.Entropy (EntropyAC(runEntropyAC))
import Test.HAPI.Effect.Orchestration (runOrchestrationViaBytes)
import Test.HAPI.Effect.Orchestration.Labels (EntropySupply, QVSSupply)
import qualified Data.ByteString as BS
import Data.Word (Word8)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.ApiTrace (ApiTrace)
import Test.HAPI.Util.ByteSupplier (mkBiDirBS, biDirLength, BiDirBS (BiDirBS))
import qualified Control.Carrier.Trace.Ignoring as IGNORING
import qualified Control.Carrier.Trace.Printing as PRINTING
import Test.HAPI.AASTG.Effect.Trav (runTrav)

runFuzzTestNonDet :: forall api sig m. (MonadIO m, MonadFail m, Algebra sig m, ValidApiDef api) => AASTG api Arbitrary -> m ()
runFuzzTestNonDet aastg = runEnvIO $ do
  let s = synthStub aastg
  debug $ show (length s)
  debug $ show (length (outPaths 0 aastg))
  forM_ s $ \stub -> do id
    $ runGenIO
    $ runError @PropertyError (fail . show) pure
    $ runProperty @PropertyA
    $ runWriter @(ApiTrace api) (\w _ -> return w)
    $ IGNORING.runTrace
    $ runForeign (fail . show)
    $ runApiFFI @api
    $ runState (\s a -> return a) PS.emptyPState
    $ runQVSFuzzArbitraryAC stub


data TRACE_MODE = IGNORING | PRINTING
  deriving (Eq, Ord, Show, Enum)


runFuzzTest :: forall api sig m.
             ( MonadIO m
             , MonadFail m
             , Algebra sig m
             , ValidApiDef api)
          => AASTG api Fuzzable
          -> ByteString
          -> m ()
runFuzzTest aastg bs
  | entropy < 128 || qvs < 128 = return ()
  | otherwise
    = runEnvIO
    $ void
    $ runError @PropertyError (fail . show) pure
    $ runProperty @PropertyA
    $ runForeign (fail . show)
    $ runApiFFI @api
    $ runState (\s a -> return a) PS.emptyPState
    $ runState @BiDirBS (\s a -> return a) supply
    $ runOrchestrationViaBytes @QVSSupply     @BiDirBS (fail . show)
    $ runQVSFromOrchestrationAC
    $ runOrchestrationViaBytes @EntropySupply @BiDirBS (fail . show)
    $ runEntropyAC
    $ runTrav @api @Fuzzable execEntropyFuzzerHandler
      stub
  where
    stub           = synthEntropyStub @api @Fuzzable aastg
    supply         = mkBiDirBS bs
    (qvs, entropy) = biDirLength supply

runFuzzTrace :: forall api sig m.
              ( MonadIO m
              , MonadFail m
              , Algebra sig m
              , ValidApiDef api)
           => AASTG api Fuzzable
           -> ByteString
           -> m ()
runFuzzTrace aastg bs
  | entropy < 128 || qvs < 128 = return ()
  | otherwise
    = do
      trace <- runEnvIO
        $ runError @PropertyError (fail . show) pure
        $ runProperty @PropertyA
        $ runWriter @(ApiTrace api) (\w _ -> return w)
        $ PRINTING.runTrace
        $ runForeign (fail . show)
        $ runApiTrace @api
        $ runState (\s a -> return a) PS.emptyPState
        $ runState @BiDirBS (\s a -> return a) supply
        $ runOrchestrationViaBytes @QVSSupply     @BiDirBS (fail . show)
        $ runQVSFromOrchestrationAC
        $ runOrchestrationViaBytes @EntropySupply @BiDirBS (fail . show)
        $ runEntropyAC
        $ runTrav @api @Fuzzable execEntropyTraceHandler
        stub
      liftIO $ print trace
      return ()
  where
    stub           = synthEntropyStub @api @Fuzzable aastg
    supply         = mkBiDirBS bs
    (qvs, entropy) = biDirLength supply
