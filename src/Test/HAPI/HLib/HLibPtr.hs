{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.HAPI.HLib.HLibPtr where
import Test.HAPI.Api (ApiDefinition, ApiName (..), HasForeignDef (..), implE)
import Test.HAPI (VPtr, vPtr2Ptr)
import Foreign (Storable (poke, peek))
import Data.SOP ( K(..), NP(..) )
import Text.Printf (printf)
import Control.Effect.State (gets)
import Control.Effect.Error (throwError)
import Control.Monad.IO.Class (liftIO)

data HLibPtr :: ApiDefinition where
  PeekPtr :: (Storable a) => HLibPtr '[VPtr a]    a
  PokePtr :: (Storable a) => HLibPtr '[VPtr a, a] ()

deriving instance Show (HLibPtr p a)
deriving instance Eq   (HLibPtr p a)
instance ApiName  HLibPtr where
  apiName PeekPtr = "*(peek)"
  apiName PokePtr = "*(poke)"

  showApiFromPat PeekPtr (K p :* Nil)
    = "*" <> p
  showApiFromPat PokePtr (K p :* K a :* Nil)
    = printf "*%s = %s" p a


instance HasForeignDef HLibPtr where
  evalForeign PeekPtr = implE $ \vp -> do
    mp <- gets $ vPtr2Ptr vp
    case mp of
      Nothing -> throwError "Peek an unknown vptr"
      Just p  -> liftIO $ peek p

  evalForeign PokePtr = implE $ \vp v -> do
    mp <- gets $ vPtr2Ptr vp
    case mp of
      Nothing -> throwError "Poke an unknown vptr"
      Just p  -> liftIO $ poke p v
