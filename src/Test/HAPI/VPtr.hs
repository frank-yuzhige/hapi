{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.HAPI.VPtr where

import Foreign (Ptr, plusPtr)
import GHC.Generics (Generic)
import Data.Data (Typeable)
import Data.Serialize (Serialize)
import Data.Functor.Identity (Identity)

import qualified Data.TypeRepMap as TM
import qualified Data.Map.Strict as M
import Control.Algebra (Has)

data VPtr t = VPtr String | VOffset (VPtr t) Int
  deriving (Eq, Ord, Show, Generic)

instance Serialize (VPtr t)

data VPtrTableEntry t = VPtrTableEntry {
  getVPtr2PtrMap :: M.Map String (Ptr t),
  getPtr2VPtrMap :: M.Map (Ptr t) String
}

newtype VPtrTable = VPtrTable { getVPtrTables :: TM.TypeRepMap VPtrTableEntry }

empty :: VPtrTable
empty = VPtrTable TM.empty

storePtr :: forall t. (Typeable t) => String -> Ptr t -> VPtrTable -> VPtrTable
storePtr x ptr (VPtrTable tables) = VPtrTable $ case TM.lookup @t tables of
  Nothing                    -> TM.insert (VPtrTableEntry (M.singleton x ptr) (M.singleton ptr x)) tables
  Just (VPtrTableEntry vp p) -> TM.insert (VPtrTableEntry (M.insert x ptr vp) (M.insert ptr x  p)) tables

vPtr2Ptr :: forall t. (Typeable t) => VPtr t -> VPtrTable -> Maybe (Ptr t)
vPtr2Ptr (VPtr x) (VPtrTable tables) = do
  VPtrTableEntry m _ <- TM.lookup @t tables
  M.lookup x m
vPtr2Ptr (VOffset v n) vpt = fmap (`plusPtr` n) (vPtr2Ptr v vpt)

ptr2VPtr :: forall t. (Typeable t) => Ptr t -> VPtrTable -> Maybe (VPtr t)
ptr2VPtr ptr (VPtrTable tables) = do
  VPtrTableEntry _ m <- TM.lookup @t tables
  x <- M.lookup ptr m
  return $ VPtr x -- TODO offset
