{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module Test.HAPI.Util.ByteSupplier where

import Data.Kind (Type)
import Data.ByteString (ByteString)
import Data.Word (Word8)
import qualified Data.ByteString as BS
import qualified Data.Serialize as S

newtype ByteSupplierError = CerealError String
  deriving Show

class Show b => ByteSupplier l b | b -> l where
  eatBytes  :: l -> S.Get a -> b -> Either ByteSupplierError (a, b)
  remainLen :: l -> b -> Int

data BiDir = FW | BW
  deriving (Eq, Ord, Enum, Show)

eatForward :: ByteSupplier BiDir b => S.Get a -> b -> Either ByteSupplierError (a, b)
eatForward  = eatBytes FW

eatBackward :: ByteSupplier BiDir b => S.Get a -> b -> Either ByteSupplierError (a, b)
eatBackward = eatBytes BW


-- Basic forward-backward bytes supplier
data FBSupplier = FBSupplier { fwBS :: ByteString, bwBS :: ByteString }

mkFBSupplier :: ByteString -> FBSupplier
mkFBSupplier bs = FBSupplier fw (BS.reverse bw)
  where
    (fw, bw) = BS.breakEnd (== magicSeparator) bs

fbSupplierLength :: FBSupplier -> (Int, Int)
fbSupplierLength (FBSupplier fw bw) = (BS.length fw, BS.length bw)

deriving instance Show FBSupplier

instance ByteSupplier BiDir FBSupplier where
  eatBytes FW get (FBSupplier fw bw) = case S.runGetState get fw 0 of
    Left err       -> Left  (CerealError err)
    Right (a, fw') -> Right (a, FBSupplier fw' bw)
  eatBytes BW get (FBSupplier fw bw) = case S.runGetState get bw 0 of
    Left err       -> Left  (CerealError err)
    Right (a, bw') -> Right (a, FBSupplier fw bw')

  remainLen FW (FBSupplier fw _ ) = BS.length fw
  remainLen BW (FBSupplier _  bw) = BS.length bw

-- Entropy + QVS Byte Supplier
data EQSupplier = EQSupplier { eqFwBS :: ByteString, eqBwBS :: ByteString, originalBw :: ByteString }

mkEQBS :: ByteString -> EQSupplier
mkEQBS bs = EQSupplier fw bw' bw'
  where
    (fw, bw) = BS.breakEnd (== magicSeparator) bs
    bw'      = BS.reverse bw

instance ByteSupplier BiDir EQSupplier where
  eatBytes FW get (EQSupplier fw bw bwo) = case S.runGetState get fw 0 of
    Left err       -> Left  (CerealError err)
    Right (a, fw') -> Right (a, EQSupplier fw' bw bwo)
  eatBytes BW get (EQSupplier fw bw bwo) = case S.runGetState get bw 0 of
    Left err       -> eatBytes BW get (EQSupplier fw (resample bw bwo) bwo)
    Right (a, bw') -> Right (a, EQSupplier fw bw' bwo)
    where
      resample bw bwo = foldr ($) bw (replicate ((200 `quot` BS.length bwo) `max` 1) (<> bwo))

  remainLen FW (EQSupplier fw _ _) = BS.length fw
  remainLen BW (EQSupplier _  _ bwo)
    | BS.null bwo = 0
    | otherwise   = maxBound -- Effectively infinite as we are reusing BW

deriving instance Show EQSupplier

magicSeparator :: Word8
magicSeparator = 0xFF
