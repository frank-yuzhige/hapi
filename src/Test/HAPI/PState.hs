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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}

module Test.HAPI.PState where
import Prelude hiding (lookup)
import Test.HAPI.DataType (TypeSpec, TyIn, TyMember)
import Data.Kind (Type)
import Control.Algebra (Has, type (:+:))
import Control.Effect.State (State)
import Control.Carrier.Fresh.Church (Fresh)
import Control.Effect.Labelled (Labelled)
import Data.Data (Proxy(Proxy), Typeable, typeOf)

import qualified Data.Map.Strict as M
import GHC.TypeNats (Nat, KnownNat, natVal)
import qualified Data.TypeRepMap as TM
import GHC.Base (Symbol)
import Data.Functor.Identity (Identity)

data PKey t = PKey { getPKeyID :: Int }
  deriving (Eq, Ord, Show)

newtype PTable t = PTable { getMap :: M.Map (PKey t) t }

newtype PState = PState { getPTables :: TM.TypeRepMap PTable }
  deriving (Show)

empty :: PState
empty = PState TM.empty

class (Typeable t) => PStateSupports s t where
  record  :: PKey t -> t -> s -> s
  lookUp  :: PKey t -> s -> Maybe t

instance (Typeable t) => PStateSupports PState t where
  record k v (PState ts) = PState $ case TM.lookup @t ts of
    Nothing         -> TM.insert (PTable (M.singleton k v)) ts
    Just (PTable m) -> TM.insert (PTable (M.insert k v m)) ts
  lookUp k (PState ts) = TM.lookup @t ts >>= (M.lookup k . getMap)
