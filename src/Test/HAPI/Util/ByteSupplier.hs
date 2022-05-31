{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}

module Test.HAPI.Util.ByteSupplier where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Kind (Type)
import qualified Data.Serialize as S
import Data.Word (Word8, Word64)
import qualified Test.HAPI.Serialize as HS
import Control.Monad (replicateM)

data ByteSupplierError
  = CerealError String
  | ByteSupplierInternalError String
  deriving (Show)

class Show b => ByteSupplier l b | b -> l where
  eatBytes :: l -> S.Get a -> b -> Either ByteSupplierError (a, b)
  remainLen :: l -> b -> Int

data BiDir = FW | BW
  deriving (Eq, Ord, Enum, Show)

eatForward :: ByteSupplier BiDir b => S.Get a -> b -> Either ByteSupplierError (a, b)
eatForward = eatBytes FW

eatBackward :: ByteSupplier BiDir b => S.Get a -> b -> Either ByteSupplierError (a, b)
eatBackward = eatBytes BW

-- Basic forward-backward bytes supplier
data FBSupplier = FBSupplier {fwBS :: ByteString, bwBS :: ByteString}

mkFBSupplier :: ByteString -> FBSupplier
mkFBSupplier bs = FBSupplier fw (BS.reverse bw)
  where
    (fw, bw) = BS.breakEnd (== magicSeparator) bs

fbSupplierLength :: FBSupplier -> (Int, Int)
fbSupplierLength (FBSupplier fw bw) = (BS.length fw, BS.length bw)

deriving instance Show FBSupplier

instance ByteSupplier BiDir FBSupplier where
  eatBytes FW getter (FBSupplier fw bw) = case S.runGetState getter fw 0 of
    Left err -> Left (CerealError err)
    Right (a, fw') -> Right (a, FBSupplier fw' bw)
  eatBytes BW getter (FBSupplier fw bw) = case S.runGetState getter bw 0 of
    Left err -> Left (CerealError err)
    Right (a, bw') -> Right (a, FBSupplier fw bw')

  remainLen FW (FBSupplier fw _) = BS.length fw
  remainLen BW (FBSupplier _ bw) = BS.length bw

-- Entropy + QVS Byte Supplier
data EQSupplier = EQSupplier {eqFwBS :: ByteString, eqBwBS :: ByteString, originalFW :: ByteString}

mkEQBS :: ByteString -> EQSupplier
mkEQBS bs = EQSupplier fw bw fw
  where
    (fw', bw) = BS.breakEnd (== magicSeparator) bs
    fw | BS.null fw' = ""
       | otherwise   = BS.init fw'  -- remove trailing '/255' to add more randomness to QVS supply

instance ByteSupplier BiDir EQSupplier where
  eatBytes FW getter (EQSupplier fw bw fwo) = case S.runGetState getter fw 0 of
    Left err
      | BS.length fw >= 32768 -> Left (CerealError err)
      | otherwise             -> eatBytes FW getter (EQSupplier resample bw fwo)
      where
        resample = foldr ($!) fw (replicate ((1024 `quot` BS.length fwo) `max` 1) (<> fwo))
    Right (a, fw') -> Right (a, EQSupplier fw' bw fwo)

  eatBytes BW getter (EQSupplier fw bw fwo) = case S.runGetState getter bw 0 of
    Left err       ->  Left (CerealError err)
    Right (a, bw') -> Right (a, EQSupplier fw bw' fwo)

  remainLen FW (EQSupplier _ _ fwo)
    | BS.null fwo = 0
    | otherwise   = maxBound -- Effectively infinite as we are reusing FW
  remainLen BW (EQSupplier _ bw _) = BS.length bw

deriving instance Show EQSupplier

magicSeparator :: Word8
magicSeparator = 0xFF

eq = mkEQBS $ "\255" <> "\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\164\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\229\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\228\&5555555555555555555\140\216\DC2\NUL\NUL\NUL\NUL\NUL555555555555554\NAK555iiiii555555\205\&55555555555*5$555555555555555550000000000089694392858552\140\216\DC2\NUL\NUL\NUL\NUL\NUL545\NAK5555555555\n"
-- tget :: S.Get String
-- tget = do
--   x <- HS.hget @Word64
--   go [] (abs $ x `mod` 64)
--   where
--   go as 0 = return $! reverse as
--   go as i = do
--     !x <- HS.hget
--     go (x:as) (i - 1)

xx = do
  (a1, b) <- eatBackward (S.get @Word8) eq
  (a2, b) <- eatBackward (S.get @Word8) b
  (a3, b) <- eatBackward (S.get @Word8) b
  (a4, b) <- eatBackward (S.get @Word8) b
  (a5, b) <- eatBackward (S.get @Word8) b
  (a6, b) <- eatBackward (S.get @Word8) b
  (a7, b) <- eatBackward (S.get @Word8) b
  return (a1, a2, a3, a4, a5, a6, a7)
