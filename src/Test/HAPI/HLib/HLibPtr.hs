{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.HAPI.HLib.HLibPtr where
import Test.HAPI.Api (ApiDefinition, ApiName (..), HasForeignDef (..), implE, showApiFromPatDefault)
import Test.HAPI (VPtr, vPtr2Ptr)
import Foreign (Storable (poke, peek), Ptr, castPtr, plusPtr, minusPtr, malloc, mallocBytes, free)
import Data.SOP ( K(..), NP(..) )
import Text.Printf (printf)
import Control.Effect.State (gets)
import Control.Effect.Error (throwError)
import Control.Monad.IO.Class (liftIO)

data HLibPtr :: ApiDefinition where
  -- Standard Ptr Operation
  CastPtr  :: HLibPtr '[Ptr a]        (Ptr b)
  PlusPtr  :: HLibPtr '[Ptr a, Int]   (Ptr a)
  MinusPtr :: HLibPtr '[Ptr a, Ptr b] Int

  -- Ptr Marshalling
  PeekPtr :: (Storable a) => HLibPtr '[Ptr a]    a
  PokePtr :: (Storable a) => HLibPtr '[Ptr a, a] ()

  -- Memory Allocation
  Malloc       :: (Storable a) => HLibPtr '[]           (Ptr a)
  -- Calloc       :: (Storable a) => HLibPtr '[]           (Ptr a)
  -- Realloc      :: (Storable a) => HLibPtr '[Ptr a]      (Ptr a)
  MallocBytes  ::                 HLibPtr '[Int]        (Ptr a)
  -- CallocBytes  ::                 HLibPtr '[Int]        (Ptr a)
  -- ReallocBytes ::                 HLibPtr '[Ptr a, Int] (Ptr a)
  Free         ::                 HLibPtr '[Ptr a]      ()



deriving instance Show (HLibPtr p a)
deriving instance Eq   (HLibPtr p a)
instance ApiName  HLibPtr where

  showApiFromPat PeekPtr (K p :* Nil)
    = "*" <> p
  showApiFromPat PokePtr (K p :* K a :* Nil)
    = printf "*%s = %s" p a
  showApiFromPat CastPtr (K a :* Nil)
    = printf ""
  showApiFromPat p a = showApiFromPatDefault p a


instance HasForeignDef HLibPtr where
  evalForeign PeekPtr     = implE $ liftIO     . peek
  evalForeign PokePtr     = implE $ (liftIO .) . poke
  evalForeign CastPtr     = implE $ return     . castPtr
  evalForeign PlusPtr     = implE $ (return .) . plusPtr
  evalForeign MinusPtr    = implE $ (return .) . minusPtr
  evalForeign Malloc      = implE $ liftIO   malloc
  evalForeign MallocBytes = implE $ liftIO . mallocBytes
  evalForeign Free        = implE $ liftIO . free

