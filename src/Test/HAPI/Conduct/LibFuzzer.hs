{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.Conduct.LibFuzzer where

import Test.HAPI.AASTG.Core ( AASTG )
import qualified Data.ByteString as BS
import Foreign.C (CString, CSize, CInt)
import Test.HAPI.Api (ValidApiDef, runForeign)
import Test.HAPI.Common ( Fuzzable )
import Options.Applicative (Parser, strArgument, help, info, (<**>), helper, fullDesc, progDesc, header, execParser, metavar, switch, long, short, showDefault, value)
import Control.Monad (when, void)
import Test.HAPI.AASTG.GraphViz (previewAASTG)
import Language.C (CConst, CExpr, Pretty (pretty))
import Test.HAPI.Constraint (CMembers, type (:<>:))
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Test.HAPI.Constraint (type (:>>>:))
import Control.Algebra (Algebra)
import Data.ByteString (ByteString)
import Test.HAPI.Effect (PropertyError, PropertyA, runEnvIO, runProperty, runApiFFI, runOrchestrationViaBytes, QVSFromOrchestrationAC (runQVSFromOrchestrationAC), EntropyAC (runEntropyAC), runApiTrace)
import Test.HAPI.ApiTrace (ApiTrace)
import qualified Control.Carrier.Trace.Printing as PRINTING
import Test.HAPI.Util.ByteSupplier (BiDirBS(..), mkBiDirBS, biDirLength)
import qualified Test.HAPI.PState as PS
import Test.HAPI.Effect.Orchestration.Labels (QVSSupply, EntropySupply)
import Control.Carrier.Error.Church (runError)
import Control.Carrier.State.Church (runState)
import Test.HAPI.AASTG.Synth (synthEntropyStub, execEntropyTraceHandler, execEntropyFuzzerHandler)
import Control.Carrier.Writer.Church (runWriter)
import Test.HAPI.AASTG.Effect.Trav (runTrav)
import qualified Test.HAPI.ApiTrace.CodeGen.C as C

data LibFuzzerConduct = LibFuzzerConduct
  { llvmFuzzerTestOneInputM :: CString -> CSize -> IO CInt
  , mainM                   :: IO ()
  }


libFuzzerConductViaAASTG :: (ValidApiDef api) => AASTG api (Fuzzable :<>: CCodeGen) -> LibFuzzerConduct
libFuzzerConductViaAASTG aastg = LibFuzzerConduct
  { llvmFuzzerTestOneInputM = _llvmFuzzerTestOneInputM aastg
  , mainM                   = _traceMainM aastg
  }

_llvmFuzzerTestOneInputM :: ( ValidApiDef api
                            , CMembers Fuzzable c) => AASTG api c -> CString -> CSize -> IO CInt
_llvmFuzzerTestOneInputM aastg str size = do
  bs <- BS.packCStringLen (str, fromIntegral size)
  runFuzzTest aastg bs
  return 0

_traceMainM :: ( ValidApiDef api
               , CMembers (CCodeGen :<>: Fuzzable) c) => AASTG api c -> IO ()
_traceMainM aastg = do
  opt <- execParser opts
  let path = crashPath opt
  bs <- BS.readFile path
  when (preview opt) (previewAASTG aastg)
  runFuzzTrace aastg bs
  where
    opts = info (traceOpt <**> helper)
      (  fullDesc
      <> progDesc "Read crash file generated by LibFuzzer, and generate code"
      <> header   "HAPI LibFuzzer Tracer" )

data TraceOpt = TraceOpt
  { crashPath :: !FilePath
  , preview   :: !Bool
  }

traceOpt :: Parser TraceOpt
traceOpt = TraceOpt
  <$> strArgument (metavar "PATH" <> help "LibFuzzer generated crash file location")
  <*> switch      (long "preview" <> short 'p' <> help "To preview AASTG" <> showDefault)



runFuzzTest :: forall api c sig m.
             ( MonadIO m
             , MonadFail m
             , Algebra sig m
             , c :>>>: Fuzzable
             , ValidApiDef api)
          => AASTG api c
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
    $ runQVSFromOrchestrationAC @c
    $ runOrchestrationViaBytes @EntropySupply @BiDirBS (fail . show)
    $ runEntropyAC
    $ runTrav @api @c execEntropyFuzzerHandler
      stub
  where
    stub           = synthEntropyStub @api @c aastg
    supply         = mkBiDirBS bs
    (qvs, entropy) = biDirLength supply

runFuzzTrace :: forall api c sig m.
              ( MonadIO m
              , MonadFail m
              , Algebra sig m
              , c :>>>: Fuzzable
              , c :>>>: CCodeGen
              , ValidApiDef api)
           => AASTG api c
           -> ByteString
           -> m ()
runFuzzTrace aastg bs
  | entropy < 128 || qvs < 128 = return ()
  | otherwise
    = do
      trace <- runEnvIO
        $ runError @PropertyError (fail . show) pure
        $ runProperty @PropertyA
        $ runWriter @(ApiTrace api c) (\w _ -> return w)
        $ PRINTING.runTrace
        $ runForeign (fail . show)
        $ runApiTrace @api
        $ runState (\s a -> return a) PS.emptyPState
        $ runState @BiDirBS (\s a -> return a) supply
        $ runOrchestrationViaBytes @QVSSupply     @BiDirBS (fail . show)
        $ runQVSFromOrchestrationAC @c
        $ runOrchestrationViaBytes @EntropySupply @BiDirBS (fail . show)
        $ runEntropyAC
        $ runTrav @api @c execEntropyTraceHandler
        stub
      let fn = C.entryFun "main" trace
          pp = pretty fn
      liftIO $ print pp
      return ()
  where
    stub           = synthEntropyStub @api @c aastg
    supply         = mkBiDirBS bs
    (qvs, entropy) = biDirLength supply