{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.HAPI.HLib.HLibCString where
import Test.HAPI.Api (ApiDefinition, ApiName, HasForeignDef (..), implE)
import Foreign
import Foreign.C
import Control.Monad.IO.Class (liftIO)

data HLibCString :: ApiDefinition where
  PeekCString    :: HLibCString '[Ptr CChar]      String
  PeekCStringLen :: HLibCString '[Ptr CChar, Int] String
  NewCString     :: HLibCString '[String]         (Ptr CChar)
  StringLen      :: HLibCString '[String]         Int
  NewCBytes      :: HLibCString '[String]         (Ptr CChar)
  CBytesLen      :: HLibCString '[String]         Int

deriving instance Show (HLibCString p a)
deriving instance Eq   (HLibCString p a)
instance ApiName  HLibCString where

instance HasForeignDef HLibCString where
  evalForeign PeekCString    = implE $ liftIO . peekCString
  evalForeign PeekCStringLen = implE $ \p l -> liftIO $ peekCStringLen (p, l)
  evalForeign NewCString     = implE $ \s   -> liftIO $ newCString s
  evalForeign StringLen      = implE $ return . length . takeWhile (/= '\NUL')
  evalForeign NewCBytes      = implE $ \s   -> liftIO $ fst <$> newCStringLen s
  evalForeign CBytesLen      = implE $ return . length
