{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}

module Test.HAPI.Conduct.LibFuzzer where

import Test.HAPI.AASTG.Core ( AASTG )
import qualified Data.ByteString as BS
import Foreign.C (CString, CSize, CInt)
import Test.HAPI.Api (ValidApiDef, runForeign)
import Test.HAPI.Common ( Fuzzable )
import Options.Applicative (Parser, strArgument, help, info, (<**>), helper, fullDesc, progDesc, header, execParser, metavar, switch, long, short, showDefault, value, strOption)
import Control.Monad (when, void, unless)
import Test.HAPI.AASTG.GraphViz (previewAASTG, aastg2GraphViz, toGraph)
import Language.C (CConst, CExpr, Pretty (pretty))
import Test.HAPI.Constraint ( CMembers, type (:<>:), type (:>>>:) )
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Algebra (Algebra)
import Data.ByteString (ByteString)
import Test.HAPI.Effect.Api ( runApiFFI, runApiTrace )
import Test.HAPI.Effect.Eff ( runEnvIO, debug, runEnvIODebug )
import Test.HAPI.Effect.Entropy ( EntropyAC(runEntropyAC), EntropyCounter (EntropyCounter) )
import Test.HAPI.Effect.Orchestration ( runOrchestrationViaBytes )
import Test.HAPI.Effect.Property
    ( PropertyA, PropertyError, runProperty, runPropertyTrace )
import Test.HAPI.Effect.EVS
    ( EVSFromOrchestrationAC(runEVSFromOrchestrationAC), EVSError )
import Test.HAPI.ApiTrace.CodeGen.C.Data ( Entry2BlockC )
import Test.HAPI.ApiTrace.Core ( ApiTrace )
import qualified Control.Carrier.Trace.Printing as PRINTING
import Test.HAPI.Util.ByteSupplier (EQSupplier (EQSupplier), mkEQBS, BiDir (..), ByteSupplier (remainLen))
import qualified Test.HAPI.PState as PS
import Test.HAPI.Effect.Orchestration.Labels (EVSSupply, EntropySupply, LabelConsumeDir (labelConsumeDir))
import Control.Carrier.Error.Church (runError)
import Control.Carrier.State.Church (runState)
import Test.HAPI.AASTG.Synth (synthEntropyStub, execEntropyFuzzerHandler, EntropyStubResult (ENTROPY_EXHAUST))
import Control.Carrier.Writer.Church (runWriter)
import Test.HAPI.AASTG.Effect.Trav (runTrav)
import qualified Test.HAPI.ApiTrace.CodeGen.C.Data as C
import Data.Data (Typeable)
import Test.HAPI.Serialize (HSerialize)
import qualified Test.HAPI.ApiTrace.CodeGen.C.Emit as C
import qualified Data.Text.IO as T
import Text.Printf (printf)
import Test.HAPI.Effect.VarUpdate (runVarUpdateTrace, VarUpdateError (VarUpdateError), runVarUpdateEval)
import Test.HAPI.Run (TRACE_MODE(IGNORING, PRINTING))
import qualified Control.Carrier.Trace.Ignoring as IGNORING
import Data.GraphViz.Commands.IO (writeDotFile)
import System.Directory (makeAbsolute)
import Data.GraphViz (GraphvizParams(..), setDirectedness, graphToDot, nonClusteredParams, toLabel)
import Data.Graph.Inductive (Gr)
import Control.Carrier.Interpret (runInterpret)
import Control.Effect.Trace (Trace(Trace))
import Data.Functor (($>))

data LibFuzzerConduct = LibFuzzerConduct
  { llvmFuzzerTestOneInputM :: CString -> CSize -> IO CInt
  , llvmFuzzerDebugM        :: CString -> CSize -> IO CInt
  , mainM                   :: IO ()
  }


libFuzzerConductViaAASTG :: ( ValidApiDef api
                            , Entry2BlockC api
                            , CMembers (HSerialize :<>: CCodeGen) c
                            , c Bool
                            , Typeable c)
                         => [String] -> AASTG api c -> LibFuzzerConduct
libFuzzerConductViaAASTG headers aastg = LibFuzzerConduct
  { llvmFuzzerTestOneInputM = _llvmFuzzerTestOneInputM aastg False
  , llvmFuzzerDebugM        = _llvmFuzzerTestOneInputM aastg True
  , mainM                   = _traceMainM headers aastg
  }

_llvmFuzzerTestOneInputM :: ( ValidApiDef api
                            , CMembers HSerialize c
                            , Typeable c)
                         => AASTG api c -> Bool -> CString -> CSize -> IO CInt
_llvmFuzzerTestOneInputM aastg dbg str size = do
  bs <- BS.packCStringLen (str, fromIntegral size)
  runFuzzTest aastg bs dbg
  return 0

_traceMainM :: ( ValidApiDef api
               , CMembers (CCodeGen :<>: HSerialize) c
               , Typeable c
               , c Bool
               , Entry2BlockC api)
            => [String] -> AASTG api c -> IO ()
_traceMainM headers aastg = do
  opt <- execParser opts
  when (previewGraph opt) (previewAASTG aastg)
  unless (null $ graphFilePath opt) $ do
    let g      = toGraph @Gr aastg
        params = nonClusteredParams { fmtNode = \ (_,l) -> [toLabel l]
                                    , fmtEdge = \ (_, _, l) -> [toLabel l]
                                    }
        dg     = setDirectedness graphToDot params g
    path <- makeAbsolute (graphFilePath opt)
    writeDotFile path dg
  case bsFilePath opt of
    ""   -> return ()
    path -> do
      bs <- BS.readFile path
      runFuzzTrace aastg bs headers
  where
    opts = info (traceOpt <**> helper)
      (  fullDesc
      <> progDesc "Read crash file generated by LibFuzzer, and generate code"
      <> header   "HAPI LibFuzzer Tracer" )

data TraceOpt = TraceOpt
  { bsFilePath    :: !FilePath
  , previewGraph  :: !Bool
  , graphFilePath :: !FilePath
  }

traceOpt :: Parser TraceOpt
traceOpt = TraceOpt
  <$> strArgument (metavar "PATH" <> help "LibFuzzer generated crash file location" <> value "")
  <*> switch      (long "preview" <> short 'p' <> help "To preview AASTG" <> showDefault)
  <*> strOption   (metavar "DPATH" <> long "dot-path" <> short 'd' <> help "AASTG Dot Graph output location" <> value "")



runFuzzTest :: forall api c sig m.
             ( MonadIO m
             , MonadFail m
             , Algebra sig m
             , CMembers HSerialize c
             , Typeable c
             , ValidApiDef api)
          => AASTG api c
          -> ByteString
          -> Bool             -- is debug
          -> m ()
runFuzzTest aastg bs dbg
  | entropy < 128 || qvs == 0 = return ()
  | otherwise = (if dbg then runEnvIODebug else runEnvIO) $ do
    debug $ printf "Running HAPI libfuzzer in debug mode..."
    qvsErr <- runError @EVSError (return . Left . show) return
      $ runError @PropertyError  (fail . show) pure
      $ runError @VarUpdateError (fail . show) pure
      $ runState (\s a -> return a) PS.emptyPState
      $ runProperty @(PropertyA c)
      $ runForeign (return . Left . show) (return . Right)
      $ runInterpret (\_ r@(Trace t) ctx -> when dbg (liftIO $ putStrLn t) $> (ctx $> ()))
      $ runApiFFI @api @c
      $ runVarUpdateEval @api @c
      $ runState @EQSupplier (\s a -> return a) supply
      $ runOrchestrationViaBytes @EVSSupply     @EQSupplier
      $ runEVSFromOrchestrationAC @HSerialize @c
      $ runOrchestrationViaBytes @EntropySupply @EQSupplier
      $ runState @EntropyCounter (\s a -> return a) 0
      $ runEntropyAC
      $ runTrav @api @c execEntropyFuzzerHandler
      $ synthEntropyStub @api @c aastg
    -- return ()
    case qvsErr of
      Left err              -> debug $ printf "error: %s" err
      Right ENTROPY_EXHAUST -> debug $ printf "bad libfuzzer input causes entropy to exhaust, supply=%s" (show supply)
      _ -> return ()
  where
    -- stub           = synthEntropyStub @api @c aastg
    supply         = mkEQBS bs
    [qvs, entropy] = map (`remainLen` supply) [labelConsumeDir @EVSSupply, labelConsumeDir @EntropySupply]

runFuzzTrace :: forall api c sig m.
              ( MonadIO m
              , MonadFail m
              , Algebra sig m
              , CMembers (CCodeGen :<>: HSerialize) c
              , c Bool
              , Typeable c
              , ValidApiDef api
              , Entry2BlockC api)
           => AASTG api c
           -> ByteString
           -> [String]
           -> m ()
runFuzzTrace aastg bs headers
  | entropy < 64 || qvs < 32 = do
    liftIO $ printf "The given bytestring input cannot instantiate a fuzz test\n"
    liftIO $ printf "  - Entropy: %d (expect >= 64)\n"
    liftIO $ printf "  - EVS    : %d (expect >= 32)\n"
    return ()
  | otherwise
    = do
      trace <- runEnvIO
        $ runError @EVSError      (fail . show) pure
        $ runError @PropertyError (fail . show) pure
        $ runError @VarUpdateError (fail . show) pure
        $ runState (\s a -> return a) PS.emptyPState
        $ runWriter @(ApiTrace api c) (\w _ -> return w)
        $ runPropertyTrace @PropertyError @api @c
        $ runApiTrace @api @c
        $ runVarUpdateTrace @api @c
        $ runState @EQSupplier (\s a -> return a) supply
        $ runOrchestrationViaBytes @EVSSupply     @EQSupplier
        $ runEVSFromOrchestrationAC @HSerialize @c
        $ runOrchestrationViaBytes @EntropySupply @EQSupplier
        $ runState @EntropyCounter (\s a -> return a) 0
        $ runEntropyAC
        $ runTrav @api @c execEntropyFuzzerHandler
        stub
      let fn = C.emitCCode headers trace
      liftIO $ T.putStrLn fn
      return ()
  where
    stub           = synthEntropyStub @api @c aastg
    supply         = mkEQBS bs
    [qvs, entropy] = map (`remainLen` supply) [FW, BW]
