{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.HAPI.HLib.HLibFS where

import Test.HAPI.Api (ApiName, HasForeignDef (..), implE, ApiDefinition)
import Control.Monad.IO.Class (liftIO)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Data.ByteString (ByteString)
import Data.String (IsString(fromString))
import qualified Data.ByteString as BS


data HLibFS :: ApiDefinition where
  NewFile :: HLibFS '[String] FilePath

deriving instance Show (HLibFS p a)
deriving instance Eq   (HLibFS p a)
instance ApiName  HLibFS where

instance HasForeignDef HLibFS where
  evalForeign NewFile = implE $ \content -> liftIO $ do
    let filepath = "hapi_newfile"
    BS.writeFile filepath (fromString content)  -- Use bytestring as String needs to take care of invalid chars in different encodings -- Yuck!
    return filepath
