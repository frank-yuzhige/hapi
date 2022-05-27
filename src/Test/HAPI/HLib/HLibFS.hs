{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}

module Test.HAPI.HLib.HLibFS where

import Test.HAPI.Api (ApiName, HasForeignDef (..), implE, ApiDefinition, HasApiMeta(..), getsMeta, updateMeta)
import Control.Monad.IO.Class (liftIO)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Data.ByteString (ByteString)
import Data.String (IsString(fromString))
import Control.Lens (makeLenses, view, over)
import qualified Data.ByteString as BS


data HLibFS :: ApiDefinition where
  NewFile :: HLibFS '[String] FilePath

newtype HLibMeta = HLibMeta {_fileId :: Int}
$(makeLenses ''HLibMeta)

deriving instance Show (HLibFS p a)
deriving instance Eq   (HLibFS p a)
instance ApiName  HLibFS where

instance HasApiMeta HLibFS where
  type Meta HLibFS = HLibMeta
  initApiMeta = HLibMeta 0

instance HasForeignDef HLibFS where
  evalForeign NewFile = implE $ \content -> do
    i <- getsMeta @HLibFS (view fileId)
    updateMeta @HLibFS (over fileId (+ 1))
    liftIO $ do
      let filepath = "hapi_newfile_" <> show i
      BS.writeFile filepath (fromString content)  -- Use bytestring as String needs to take care of invalid chars in different encodings -- Yuck!
      return filepath
