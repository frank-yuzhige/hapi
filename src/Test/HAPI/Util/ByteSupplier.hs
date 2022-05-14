{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
module Test.HAPI.Util.ByteSupplier where

import Data.Kind (Type)
import Data.ByteString (ByteString)
import Data.Word (Word8)
import qualified Data.ByteString as BS
import qualified Data.Serialize as S

newtype ByteSupplierError = CerealError String
  deriving Show

class ByteSupplier l b | b -> l where
  eatBytes :: l -> S.Get a -> b -> Either ByteSupplierError (a, b)

data BiDir = FW | BW
  deriving (Eq, Ord, Enum, Show)

eatForward :: ByteSupplier BiDir b => S.Get a -> b -> Either ByteSupplierError (a, b)
eatForward  = eatBytes FW

eatBackward :: ByteSupplier BiDir b => S.Get a -> b -> Either ByteSupplierError (a, b)
eatBackward = eatBytes BW


data BiDirBS = BiDirBS { fwBS :: ByteString, bwBS :: ByteString }

mkBiDirBS :: ByteString -> BiDirBS
mkBiDirBS bs = BiDirBS fw (BS.reverse bw)
  where
    (fw, bw) = BS.breakEnd (== magicSeparator) bs

biDirLength :: BiDirBS -> (Int, Int)
biDirLength (BiDirBS fw bw) = (BS.length fw, BS.length bw)


instance ByteSupplier BiDir BiDirBS where
  eatBytes FW get (BiDirBS fw bw) = case S.runGetState get fw 0 of
    Left err       -> Left  (CerealError err)
    Right (a, fw') -> Right (a, BiDirBS fw' bw)
  eatBytes BW get (BiDirBS fw bw) = case S.runGetState get bw 0 of
    Left err       -> Left  (CerealError err)
    Right (a, bw') -> Right (a, BiDirBS fw bw')


magicSeparator :: Word8
magicSeparator = 0xFF
