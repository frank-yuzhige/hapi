{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}

module Test.HAPI.FFI where

import Control.Monad.IO.Class (MonadIO (liftIO))
import Foreign.C (CString)
import Foreign.C.Types (CInt(CInt))
import Foreign ( Ptr, Storable(poke, sizeOf), Storable(peek) )
import GHC.Generics
import Foreign.Storable (Storable(alignment))
import Foreign.CStorable (CStorable(cSizeOf, cAlignment, cPoke, cPeek))

newtype FFIO a = FFIO { unFFIO :: IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

ffi :: MonadIO m => FFIO a -> m a
ffi = liftIO . unFFIO


-- Need to use CInt instead of Int to prevent negative number underflow error
foreign import ccall "broken_add"
  add :: CInt -> CInt -> FFIO CInt
foreign import ccall "segfault_minus"
  sub :: CInt -> CInt -> FFIO CInt
foreign import ccall "stateful_multiply"
  mul :: CInt -> CInt -> FFIO CInt
foreign import ccall "limited_input_range_negate"
  neg :: CInt -> FFIO CInt


foreign import ccall "broken_str"
  str :: CInt -> FFIO CString

data Stack = Stack { top :: Int, array :: Ptr Int }
  deriving (Generic, Eq, Show)


instance CStorable Stack where
instance Storable Stack where
  sizeOf = cSizeOf
  alignment = cAlignment
  poke = cPoke
  peek = cPeek

-- TODO: pointer translation (Ptr <-> Pointer)

foreign import ccall "create_stack"
  createStack  :: FFIO (Ptr Stack)
foreign import ccall "push_stack"
  pushStack    :: Ptr Stack -> CInt -> FFIO ()
foreign import ccall "pop_stack"
  popStack     :: Ptr Stack -> FFIO ()
foreign import ccall "peek_stack"
  peekStack    :: Ptr Stack -> FFIO CInt
foreign import ccall "get_stack_size"
  getStackSize :: Ptr Stack -> FFIO CInt
