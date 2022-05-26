{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

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
import Test.HAPI.Constraint ( CMembers, type (:<>:), type (:>>>:) )
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Algebra (Algebra)
import Data.ByteString (ByteString)
import Test.HAPI.Effect.Api ( runApiFFI, runApiTrace )
import Test.HAPI.Effect.Eff ( runEnvIO )
import Test.HAPI.Effect.Entropy ( EntropyAC(runEntropyAC) )
import Test.HAPI.Effect.Orchestration ( runOrchestrationViaBytes )
import Test.HAPI.Effect.Property
    ( PropertyA, PropertyError, runProperty, runPropertyTrace )
import Test.HAPI.Effect.QVS
    ( QVSFromOrchestrationAC(runQVSFromOrchestrationAC), QVSError )
import Test.HAPI.ApiTrace.CodeGen.C.Data ( Entry2BlockC )
import Test.HAPI.ApiTrace.Core ( ApiTrace )
import qualified Control.Carrier.Trace.Printing as PRINTING
import Test.HAPI.Util.ByteSupplier (EQSupplier (EQSupplier), mkEQBS, BiDir (..), ByteSupplier (remainLen))
import qualified Test.HAPI.PState as PS
import Test.HAPI.Effect.Orchestration.Labels (QVSSupply, EntropySupply)
import Control.Carrier.Error.Church (runError)
import Control.Carrier.State.Church (runState)
import Test.HAPI.AASTG.Synth (synthEntropyStub, execEntropyFuzzerHandler)
import Control.Carrier.Writer.Church (runWriter)
import Test.HAPI.AASTG.Effect.Trav (runTrav)
import qualified Test.HAPI.ApiTrace.CodeGen.C.Data as C
import Data.Data (Typeable)
import Test.HAPI.Serialize (HSerialize)

data LibFuzzerConduct = LibFuzzerConduct
  { llvmFuzzerTestOneInputM :: CString -> CSize -> IO CInt
  , mainM                   :: IO ()
  }


libFuzzerConductViaAASTG :: ( ValidApiDef api
                            , Entry2BlockC api
                            , CMembers (HSerialize :<>: CCodeGen) c
                            , c Bool
                            , Typeable c)
                         => AASTG api c -> LibFuzzerConduct
libFuzzerConductViaAASTG aastg = LibFuzzerConduct
  { llvmFuzzerTestOneInputM = _llvmFuzzerTestOneInputM aastg
  , mainM                   = _traceMainM aastg
  }

_llvmFuzzerTestOneInputM :: ( ValidApiDef api
                            , CMembers HSerialize c
                            , Typeable c)
                         => AASTG api c -> CString -> CSize -> IO CInt
_llvmFuzzerTestOneInputM aastg str size = do
  bs <- BS.packCStringLen (str, fromIntegral size)
  runFuzzTest aastg bs
  return 0

_traceMainM :: ( ValidApiDef api
               , CMembers (CCodeGen :<>: HSerialize) c
               , Typeable c
               , c Bool
               , Entry2BlockC api)
            => AASTG api c -> IO ()
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
             , CMembers HSerialize c
             , Typeable c
             , ValidApiDef api)
          => AASTG api c
          -> ByteString
          -> m ()
runFuzzTest aastg bs
  | entropy < 64 || qvs < 32 = return ()
  | otherwise = do
    qvsErr <- runEnvIO
      $ runError @QVSError      (return . Just . show) (return . const Nothing)
      $ runError @PropertyError (fail . show) pure
      $ runState (\s a -> return a) PS.emptyPState
      $ runProperty @PropertyA
      $ runForeign (fail . show)
      $ runApiFFI @api @c
      $ runState @EQSupplier (\s a -> return a) supply
      $ runOrchestrationViaBytes @QVSSupply     @EQSupplier
      $ runQVSFromOrchestrationAC @HSerialize @c
      $ runOrchestrationViaBytes @EntropySupply @EQSupplier
      $ runEntropyAC
      $ runTrav @api @c execEntropyFuzzerHandler
        stub
    case qvsErr of
      Nothing -> return ()
      Just x  -> liftIO $ print "bad libfuzzer input causes QVS to exhaust"
  where
    stub           = synthEntropyStub @api @c aastg
    supply         = mkEQBS bs
    [entropy, qvs] = map (`remainLen` supply) [FW, BW]

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
           -> m ()
runFuzzTrace aastg bs
  | entropy < 64 || qvs < 32 = return ()
  | otherwise
    = do
      trace <- runEnvIO
        $ runError @QVSError      (fail . show) pure
        $ runError @PropertyError (fail . show) pure
        $ runState (\s a -> return a) PS.emptyPState
        $ runWriter @(ApiTrace api c) (\w _ -> return w)
        $ (runPropertyTrace @PropertyError @api @c)
        $ runApiTrace @api @c
        $ runState @EQSupplier (\s a -> return a) supply
        $ runOrchestrationViaBytes @QVSSupply     @EQSupplier
        $ runQVSFromOrchestrationAC @HSerialize @c
        $ runOrchestrationViaBytes @EntropySupply @EQSupplier
        $ runEntropyAC
        $ runTrav @api @c execEntropyFuzzerHandler
        stub
      let fn = show $ pretty $ C.traceMain trace
      liftIO $ putStrLn fn
      return ()
  where
    stub           = synthEntropyStub @api @c aastg
    supply         = mkEQBS bs
    [entropy, qvs] = map (`remainLen` supply) [FW, BW]
