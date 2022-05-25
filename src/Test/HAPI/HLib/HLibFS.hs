{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.HAPI.HLib.HLibFS where

import Test.HAPI.Api (ApiName, HasForeignDef (..), implE, ApiDefinition)
import Control.Monad.IO.Class (liftIO)

data HLibFS :: ApiDefinition where
  NewFile :: HLibFS '[String] FilePath

deriving instance Show (HLibFS p a)
deriving instance Eq   (HLibFS p a)
instance ApiName  HLibFS where

instance HasForeignDef HLibFS where
  evalForeign NewFile = implE $ \content -> liftIO $ do
    let filepath = "hapi_newfile"
    writeFile filepath content
    return filepath
