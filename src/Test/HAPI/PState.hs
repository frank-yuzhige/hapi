{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.HAPI.PState where
import Prelude hiding (lookup)
import Test.HAPI.DataType (TypeSpec, TyIn, TyMember)
import Control.Algebra (Has, type (:+:))
import Control.Effect.State (State)
import Control.Carrier.Fresh.Church (Fresh)
import Control.Effect.Labelled (Labelled)
import GHC.TypeNats (Nat, KnownNat, natVal)
import GHC.Base (Symbol)
import Data.Functor.Identity (Identity)
import Data.String (IsString (fromString))
import Data.Data (Typeable)
import Data.Kind (Type)

import qualified Data.Map.Strict as M
import qualified Data.TypeRepMap as TM
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
newtype PKey t = PKey { getPKeyID :: String }
  deriving (Eq, Ord)

newtype PTable t = PTable { getMap :: M.Map (PKey t) t }

newtype PState = PState { getPTables :: TM.TypeRepMap PTable }
  deriving (Show)


class (Typeable t) => PStateSupports s t where
  record  :: PKey t -> t -> s -> s
  forget  :: PKey t -> s -> s
  lookUp  :: PKey t -> s -> Maybe t

empty :: PState
empty = PState TM.empty

instance (Typeable t) => PStateSupports PState t where
  record k v (PState ts) = PState $ case TM.lookup @t ts of
    Nothing         -> TM.insert (PTable (M.singleton k v)) ts
    Just (PTable m) -> TM.insert (PTable (M.insert k v m)) ts
  forget k (PState ts) = PState $ TM.delete @t ts
  lookUp k (PState ts) = TM.lookup @t ts >>= (M.lookup k . getMap)

instance Show (PKey t) where
  show = show . getPKeyID

instance IsString (PKey t) where
  fromString = PKey

deriving instance Generic  (PKey t)
deriving instance Hashable (PKey t)
