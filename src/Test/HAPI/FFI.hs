{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.HAPI.FFI where

import Control.Monad.IO.Class (MonadIO)
import Foreign.C.Types (CInt(CInt))

newtype FFIO a = FFIO { unFFIO :: IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

-- Need to use CInt instead of Int to prevent negative number underflow error
foreign import ccall "broken_add"
  add :: CInt -> CInt -> FFIO CInt
foreign import ccall "segfault_minus"
  sub :: CInt -> CInt -> FFIO CInt
foreign import ccall "stateful_multiply"
  mul :: CInt -> CInt -> FFIO CInt
foreign import ccall "limited_input_range_negate"
  neg :: CInt -> FFIO CInt


