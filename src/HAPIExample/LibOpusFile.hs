{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}

module HAPIExample.LibOpusFile where
import Test.HAPI
import Foreign.C
import Data.Data (Typeable)

import Control.Monad.IO.Class (liftIO)
import Data.ByteString (ByteString)
import Foreign
import Data.Serialize (Serialize (..))
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import GHC.Ptr (Ptr(..))

import qualified Test.HAPI.HLib.HLibPrelude as HLib
import qualified Test.HAPI.HLib.HLibPtr     as HLib
import qualified Test.HAPI.HLib.HLibCString as HLib
import qualified Test.HAPI.HLib.HLibFS      as HLib

import Test.HAPI.HLib.HLibPrelude (HLibPrelude)
import Test.HAPI.HLib.HLibPtr (HLibPtr)
import Test.HAPI.HLib.HLibCString (HLibCString)
import Test.HAPI.HLib.HLibFS (HLibFS)
import qualified Data.ByteString as BS

conduct :: LibFuzzerConduct
conduct = libFuzzerConductViaAASTG ["opusfile"] $ castAASTG g
  where
    g  = runEnv $ coalesceRuleAASTGs 500 [g1, g2]
    g1 = runEnv $ runBuildTypedAASTG @A @C gOpenFile
    g2 = runEnv $ runBuildTypedAASTG @A @C gOpenMemory

ggg :: IO (TypedAASTG A C)
ggg = runEnvIO @IO $ do
  x <- coalesceRuleAASTGs 500 [g1, g2]
  debugIO $ previewAASTG $ castAASTG x
  return x
  where
    g1 = runEnv $ runBuildTypedAASTG @A @C gOpenFile
    g2 = runEnv $ runBuildTypedAASTG @A @C gOpenMemory

-- foreign export ccall "LLVMFuzzerTestOneInput" testOneInputM
  -- :: CString -> CSize -> IO CInt

testOneInputM = llvmFuzzerTestOneInputM conduct

testOne bs = BS.useAsCStringLen bs (\(d, s) -> testOneInputM d (fromIntegral s))

runTestOne = testOne "Oggsdadasdlksd;laskd;akslkdakdsasdaskdlaskdlaskdl;sak;dakd;lak;dlsakdl;sak;ldskd;lakd;aslkdl;askd;slaksda;lkda;als;dkl;dkas;ldk\255sasdaldasldkalkdlskdsalkdsaldklkdsasdadsdadsdadsdadasddadassdaaldksakalkl"

main = mainM conduct

data OggOpusFile

-- foreign import ccall "op_free"
--   op_free :: Ptr OggOpusFile -> IO ()

-- foreign import ccall "op_test_memory"
--   op_test_memory :: Ptr CChar -> CInt -> Ptr CInt -> IO (Ptr OggOpusFile)

-- foreign import ccall "op_test_file"
--   op_test_file :: Ptr CChar -> Ptr CInt -> IO (Ptr OggOpusFile)

-- foreign import ccall "op_test_open"
--   op_test_open :: Ptr OggOpusFile -> IO CInt

-- foreign import ccall "op_channel_count"
--   op_channel_count :: Ptr OggOpusFile -> CInt -> IO CInt

-- foreign import ccall "op_pcm_total"
--   op_pcm_total :: Ptr OggOpusFile -> CInt -> IO Int64

-- foreign import ccall "op_read"
--   op_read
--     :: Ptr OggOpusFile -- _of
--     -> Ptr Int16       -- _pcm
--     -> CInt            -- _buf_size
--     -> Ptr CInt        -- _li
--     -> IO CInt

data OpusFileApi :: ApiDefinition where
  TestMemory   :: OpusFileApi '[Ptr CChar, CInt, Ptr CInt] (Ptr OggOpusFile)
  TestFile     :: OpusFileApi '[Ptr CChar, Ptr CInt]       (Ptr OggOpusFile)
  TestOpen     :: OpusFileApi '[Ptr OggOpusFile] CInt
  Free         :: OpusFileApi '[Ptr OggOpusFile] ()
  ChannelCount :: OpusFileApi '[Ptr OggOpusFile, CInt] CInt
  PcmTotal     :: OpusFileApi '[Ptr OggOpusFile, CInt] Int64
  Read         :: OpusFileApi '[Ptr OggOpusFile, Ptr Int16, CInt, Ptr CInt] CInt


deriving instance Typeable (OpusFileApi p a)
deriving instance Show     (OpusFileApi p a)
deriving instance Eq       (OpusFileApi p a)

instance ApiName      OpusFileApi where
  apiNameUnder "C" = \case
    TestMemory   -> "op_test_memory"
    TestFile     -> "op_test_file"
    TestOpen     -> "op_test_open"
    Free         -> "op_free"
    ChannelCount -> "op_channel_count"
    PcmTotal     -> "op_pcm_total"
    Read         -> "op_read"
  apiNameUnder _ = apiName

instance Entry2BlockC OpusFileApi

instance HasForeignDef OpusFileApi where
  evalForeign = \case
    TestMemory   ->  undefined -- implE $ \p x q -> liftIO $ op_test_memory p x q
    TestFile     ->  undefined -- implE $ \p q   -> liftIO $ op_test_file   p q
    TestOpen     ->  undefined -- implE $ liftIO . op_test_open
    Free         ->  undefined -- implE $ liftIO . op_free
    ChannelCount ->  undefined -- implE $ \p x -> liftIO $ op_channel_count p x
    PcmTotal     ->  undefined -- implE $ \p x -> liftIO $ op_pcm_total p x
    Read         ->  undefined -- implE $ \f p b l -> liftIO $ op_read f p b l

type A = OpusFileApi :$$: HLibPrelude :$$: HLibPtr :$$: HLibCString :$$: HLibFS

type C = Fuzzable :<>: HSerialize :<>: CCodeGen

gOpenMemory :: Eff (BuildAASTG A C) sig m => m ()
gOpenMemory = do
  ctnt  <- p <%> decl anything
  path  <- p <%> call HLib.NewFile(var ctnt)
  cp    <- p <%> call HLib.NewCString(var ctnt)
  eptr  <- p <%> call (HLib.Malloc @CInt) ()
  file  <- p <%> call TestFile(var cp, var eptr)
  p <%> ifFalse HLib.IsNullPtr(var file)
  r     <- p <%> call TestOpen(var file)
  p <%> assertTrue (HLib.==) (var r, value 0)
  gChannelCount file
  p <%> call Free(var file)
  return ()
  where p = Building @A @C

gOpenFile :: Eff (BuildAASTG A C) sig m => m ()
gOpenFile = do
  path  <- p <%> decl (value "sample3.opus")
  cp    <- p <%> call HLib.NewCString(var path)
  eptr  <- p <%> call (HLib.Malloc @CInt) ()
  file  <- p <%> call TestFile(var cp, var eptr)
  p <%> ifFalse HLib.IsNullPtr(var file)
  r     <- p <%> call TestOpen(var file)
  p <%> assertTrue (HLib.==) (var r, value 0)
  -- gChannelCount file
  p <%> call Free(var file)
  return ()
  where p = Building @A @C

gChannelCount :: Eff (BuildAASTG A C) sig m
              => PKey (Ptr OggOpusFile)
              -> m ()
gChannelCount handle = do
  c <- p <%> call ChannelCount (var handle, value (-1))
  p <%> assert (DOr (DEq True (Value 2) (Get c)) (DEq True (Value 3) (Get c)))
  -- ctnt  <- p <%> var anything
  where p = Building @A @C

instance TyConstC OggOpusFile where
  toCConst _ = undefined -- Phantom type
  toCType  _ = ctype "OggOpusFile"
