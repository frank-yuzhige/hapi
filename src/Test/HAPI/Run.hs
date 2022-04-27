{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.HAPI.Run where
import Test.HAPI.AASTG.Core (AASTG(AASTG))
import Control.Monad.IO.Class (MonadIO)
import Test.QuickCheck (Arbitrary)
import Test.HAPI.Effect.Property
    ( PropertyA, PropertyError, runProperty )
import Test.HAPI.Api (ApiTrace, runForeign, HasForeignDef, ApiName, ValidApiDef)
import qualified Test.HAPI.PState as PS
import Test.HAPI.Effect.Eff (debug, runEnvIO, Algebra)
import Test.HAPI.AASTG.Synth (synthStub, synthEntropyStub)
import Test.HAPI.AASTG.Analysis.Path (outPaths)
import Control.Monad (forM_)
import Test.HAPI.Effect.Gen (runGenIO)
import Control.Carrier.Error.Church (runError)
import Control.Carrier.Writer.Strict (runWriter)
import Control.Carrier.Trace.Printing (runTrace)
import Test.HAPI.Effect.Api (runApiFFI)
import Control.Carrier.State.Church (runState)
import Test.HAPI.Effect.QVS (runQVSFuzzArbitraryAC, QVSFromOrchestrationAC (runQVSFromOrchestrationAC))
import Data.ByteString (ByteString)
import Test.HAPI.Effect.Entropy (EntropyAC(runEntropyAC))
import Test.HAPI.Effect.Orchestration (runOrchestrationViaBytes)
import Test.HAPI.Effect.Orchestration.Labels (EntropySupply, QVSSupply)
import qualified Data.ByteString as BS
import Data.Word (Word8)
import Test.HAPI.Common (Fuzzable)

magicSeparator :: Word8
magicSeparator = 0xEF

runFuzzTestNonDet :: forall api sig m. (MonadIO m, MonadFail m, Algebra sig m, ValidApiDef api) => AASTG api Arbitrary -> m ()
runFuzzTestNonDet aastg = runEnvIO $ do
  let s = synthStub aastg
  debug $ show (length s)
  debug $ show (length (outPaths 0 aastg))
  forM_ s $ \stub -> do id
    . runGenIO
    . runError @PropertyError (fail . show) pure
    . runProperty @PropertyA
    . runWriter @(ApiTrace api)
    . runTrace
    . runForeign (fail . show)
    . runApiFFI @api
    . runState (\s a -> return a) PS.emptyPState
    . runQVSFuzzArbitraryAC
    $ stub


runFuzzTest :: forall api sig m. (MonadIO m, MonadFail m, Algebra sig m, ValidApiDef api) => AASTG api Fuzzable -> ByteString -> m ()
runFuzzTest aastg bs
  | BS.length entropy < 128 = return ()
  | BS.length qvs     < 128 = return ()
  | otherwise = runEnvIO $ do
  runGenIO
    $ runError @PropertyError (fail . show) pure
    $ runProperty @PropertyA
    $ runWriter @(ApiTrace api)
    $ runTrace
    $ runForeign (fail . show)
    $ runApiFFI @api
    $ runState (\s a -> return a) PS.emptyPState
    $ runOrchestrationViaBytes @QVSSupply (fail . show) qvs
    $ runQVSFromOrchestrationAC
    $ runOrchestrationViaBytes @EntropySupply (fail . show) entropy
    $ runEntropyAC stub
  return ()
  where
    stub = synthEntropyStub @api @Fuzzable aastg
    (entropy, qvs) = BS.break (== magicSeparator) bs
