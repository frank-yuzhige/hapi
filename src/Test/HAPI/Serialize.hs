{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
module Test.HAPI.Serialize where

import qualified Data.Serialize as S

import Control.Monad
import Data.ByteString (ByteString)
import Data.Char    (chr,ord)
import Data.List    (unfoldr)
import Data.Word
import Foreign
import Data.Monoid
import Numeric.Natural
import Data.ByteString.Short (ShortByteString)
import Data.IntSet (IntSet)
import Data.Ratio (Ratio)
import Data.IntMap (IntMap)
import Data.Graph (Tree)
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.ByteString as B
import GHC.Generics (Generic)
import GHC.Exts (Ptr(..), int2Addr#, addr2Int#, Int (..))

-- A Serialize class with a bit more "sanity" when dealing with random bytes
class S.Serialize a => HSerialize a where
  hget :: S.Get a

  default hget :: S.Serialize a => S.Get a
  hget = S.get



deriving instance Generic (Ptr a)
instance S.Serialize (Ptr a) where
  put p = S.put (castPtr2Int p)
  get   = castInt2Ptr <$> S.get @Int

castInt2Ptr :: Int -> Ptr a
castInt2Ptr (I# i) = Ptr (int2Addr# i)

castPtr2Int :: Ptr a -> Int
castPtr2Int (Ptr a) = I# (addr2Int# a)

-- TODO implement as necessary
instance HSerialize Bool
instance HSerialize Char
instance HSerialize Double
instance HSerialize Float
instance HSerialize Int
instance HSerialize Int8
instance HSerialize Int16
instance HSerialize Int32
instance HSerialize Int64
instance HSerialize Integer
instance HSerialize Ordering
instance HSerialize Word
instance HSerialize Word8
instance HSerialize Word16
instance HSerialize Word32
instance HSerialize Word64
instance HSerialize ()
instance HSerialize All
instance HSerialize Any
instance HSerialize ShortByteString
instance HSerialize ByteString where
  hget = do
    x <- hget @Int
    bs <- S.getBytes (abs $ x `mod` 1024)
    return $! B.copy bs
instance HSerialize IntSet
instance HSerialize a => HSerialize [a] where
  hget = do
    x <- hget @Word64
    go [] (abs $ x `mod` 1024)
    where
    go as 0 = return $! reverse as
    go as i = do
      !x <- hget
      go (x:as) (i - 1)

instance HSerialize (Ptr a)
instance HSerialize a => HSerialize (Maybe a)
instance (HSerialize a, Integral a) => HSerialize (Ratio a)
instance HSerialize a => HSerialize (First a)
instance HSerialize a => HSerialize (Last a)
instance HSerialize a => HSerialize (Dual a)
instance HSerialize a => HSerialize (Sum a)
instance HSerialize a => HSerialize (Product a)
instance HSerialize e => HSerialize (IntMap e)
instance HSerialize e => HSerialize (Tree e)
instance HSerialize e => HSerialize (Seq e)
instance (Ord a, HSerialize a) => HSerialize (Set a)
instance (HSerialize a, HSerialize b) => HSerialize (Either a b)
instance (HSerialize a, HSerialize b) => HSerialize (a, b)
instance (Ord k, HSerialize k, HSerialize e) => HSerialize (Map k e)
instance (HSerialize a, HSerialize b, HSerialize c) => HSerialize (a, b, c)
instance (HSerialize a, HSerialize b, HSerialize c, HSerialize d) => HSerialize (a, b, c, d)
instance (HSerialize a, HSerialize b, HSerialize c, HSerialize d, HSerialize e) => HSerialize (a, b, c, d, e)
instance (HSerialize a, HSerialize b, HSerialize c, HSerialize d, HSerialize e, HSerialize f) => HSerialize (a, b, c, d, e, f)
instance (HSerialize a, HSerialize b, HSerialize c, HSerialize d, HSerialize e, HSerialize f, HSerialize g) => HSerialize (a, b, c, d, e, f, g)
instance (HSerialize a, HSerialize b, HSerialize c, HSerialize d, HSerialize e, HSerialize f, HSerialize g, HSerialize h) => HSerialize (a, b, c, d, e, f, g, h)
instance (HSerialize a, HSerialize b, HSerialize c, HSerialize d, HSerialize e, HSerialize f, HSerialize g, HSerialize h, HSerialize i) => HSerialize (a, b, c, d, e, f, g, h, i)
instance (HSerialize a, HSerialize b, HSerialize c, HSerialize d, HSerialize e, HSerialize f, HSerialize g, HSerialize h, HSerialize i, HSerialize j) => HSerialize (a, b, c, d, e, f, g, h, i, j)
