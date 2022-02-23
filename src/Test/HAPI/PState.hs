{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.PState where
import Prelude hiding (lookup)
import Test.HAPI.DataType (TypeSpec, TyIn, TyMember)
import Data.Kind (Type)
import Control.Algebra (Has, type (:+:))
import Control.Effect.State (State)
import Control.Carrier.Fresh.Church (Fresh)
import Control.Effect.Labelled (Labelled)
import Data.TypeMap.Dynamic.Alt (TypeMap, empty, at, (<:), OfType, lookup)
import Data.Data (Proxy(Proxy), Typeable)

import qualified Data.Map as M
import qualified Data.Type.Map as TM
import GHC.TypeNats (Nat, KnownNat, natVal)
import qualified Data.Type.Map as TM
import GHC.Base (Symbol)

data PKey (n :: Nat) = PKey

instance KnownNat n => Show (PKey n) where
  show = ("PKey" <>) . show . natVal

data PMEntry k v = k :-> v

data PMap (n :: [PMEntry Nat Type]) where
  Empty :: PMap '[]
  Node  :: forall k v m. v -> PMap m -> PMap (k :-> v : m)

class PMember k t m where
  find :: PMap m -> t

instance {-# OVERLAPS #-} PMember k t (k :-> t : m) where
  find (Node x _) = x

instance {-# OVERLAPPABLE #-} PMember k t m => PMember k t (k' :-> t' : m) where
  find (Node _ x) = find @k x

class PUpdate k t m n where
  update :: t -> PMap m -> PMap n

instance {-# OVERLAPS #-} PUpdate k t (k :-> s : m) (k :-> t : m) where
  update t (Node v m) = Node t m

instance PUpdate k t m n => PUpdate k t (k' :-> s : m) (k' :-> s : n) where
  update t (Node v m) = Node v (update @k t m)

instance PUpdate k t m (k :-> t : m) where
  update t m = Node @k t m


-- y :: PMap '[1 :-> String, 2 :-> String]
-- y = update @1 "abc" (update @2 "def" Empty)
-- newtype Ref t = Ref { refID :: Integer }
--   deriving (Eq, Ord, Show)

-- data PState (ts :: [Type]) where
--   PStateNull :: PState '[]
--   PStateNode :: RefMap t -> PState ts -> PState (t : ts)

-- -- TODO Optimize me O(1)
-- class HasMap ts t where
--   getMap :: PState ts -> RefMap t

-- instance HasMap (t : ts) t where
--   getMap (PStateNode m _) = m

-- instance HasMap ts t => HasMap (t' : ts) t where
--   getMap (PStateNode _ p) = getMap p


-- lookUp :: (HasMap ts t) => PState ts -> Ref t -> Maybe t
-- lookUp p k = M.lookup k (getMap p)

-- type RefMap t = M.Map (Ref t) t

-- x :: TypeMap (OfType Int)
-- x = empty <: at @(OfType Int) 12
--           <: at @(OfType Bool) 123

-- y :: Maybe Int
-- y = lookup @(OfType Bool) x
