{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.Run where
import Test.HAPI.AASTG.Core (AASTG(AASTG))
import Control.Monad.IO.Class (MonadIO, liftIO)
import Test.QuickCheck (Arbitrary)
import Test.HAPI.Effect.Property
    ( PropertyA, PropertyError, runProperty )
import Test.HAPI.Api (runForeign, HasForeignDef, ApiName, ValidApiDef)
import qualified Test.HAPI.PState as PS
import Test.HAPI.Effect.Eff (debug, runEnvIO, Algebra)
import Test.HAPI.AASTG.Synth (synthStub, synthEntropyStub, execEntropyFuzzerHandler)
import Test.HAPI.AASTG.Analysis.Path (outPaths)
import Control.Monad (forM_, void)
import Test.HAPI.Effect.Gen (runGenIO)
import Control.Carrier.Error.Church (runError)
import Control.Carrier.Writer.Church (runWriter)
import Test.HAPI.Effect.Api (runApiFFI, runApiTrace)
import Control.Carrier.State.Church (runState)
import Test.HAPI.Effect.EVS (runEVSFuzzArbitraryAC, EVSFromOrchestrationAC (runEVSFromOrchestrationAC))
import Data.ByteString (ByteString)
import Test.HAPI.Effect.Entropy (EntropyAC(runEntropyAC))
import Test.HAPI.Effect.Orchestration (runOrchestrationViaBytes)
import Test.HAPI.Effect.Orchestration.Labels (EntropySupply, EVSSupply)
import qualified Data.ByteString as BS
import Data.Word (Word8)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.ApiTrace (ApiTrace)
import qualified Control.Carrier.Trace.Ignoring as IGNORING
import qualified Control.Carrier.Trace.Printing as PRINTING
import Test.HAPI.AASTG.Effect.Trav (runTrav)
import Test.HAPI.Constraint (type (:<>:), type (:>>>:))
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen)
import Data.Data (Typeable)
import Test.HAPI.Effect.VarUpdate (VarUpdateError(VarUpdateError), runVarUpdateEval)

runFuzzTestNonDet :: forall api c sig m.
                   ( MonadIO m
                   , MonadFail m
                   , Algebra sig m
                   , c :>>>: Arbitrary
                   , Typeable c
                   , ValidApiDef api) => AASTG api c -> m ()
runFuzzTestNonDet aastg = runEnvIO $ do
  let s = synthStub @api @c aastg
  debug $ show (length s)
  debug $ show (length (outPaths 0 aastg))
  forM_ s $ \stub -> do id
    $ runGenIO
    $ runError @PropertyError (fail . show) pure
    $ runError @VarUpdateError (fail . show) pure
    $ runState (\s a -> return a) PS.emptyPState
    $ runProperty @(PropertyA c)
    $ runWriter @(ApiTrace api Arbitrary) (\w _ -> return w)
    $ IGNORING.runTrace
    $ runForeign (fail . show) return
    $ runApiFFI @api @c
    $ runVarUpdateEval @api @c
    $ runEVSFuzzArbitraryAC @c stub


data TRACE_MODE = IGNORING | PRINTING
  deriving (Eq, Ord, Show, Enum)

