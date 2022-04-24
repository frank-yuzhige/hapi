{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE RoleAnnotations       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | Extended internal API for 'TypeRepMap' and operations on it.
-- Unfortunately, stack is too dinosaur to adopt new packages, so some important functionality provided in later versions of
-- Data.TypeRepMap is not available. I have to "re-create" them...
module Test.HAPI.Util.TypeRepMap (
  module TM,
  intersection,
  intersectionWith,
  mfold,
  foldMap,
  keysWith,
  toListWith,
) where

import qualified Data.TypeRepMap as TM
import qualified Data.TypeRepMap.Internal as TM
import Data.TypeRepMap (TypeRepMap)
import qualified Data.Map.Strict as Map
import GHC.Exts (Any, IsList (toList))
import Data.Functor.Identity (Identity(Identity))
import Type.Reflection (TypeRep, Typeable, withTypeable, typeOf, typeRep)
import Unsafe.Coerce
import Data.Hashable (Hashable (hashWithSalt))
import Prelude hiding (foldMap)

-- Extract the kind of a type. We use it to work around lack of syntax for
-- inferred type variables (which are not subject to type applications).
type KindOf (a :: k) = k

type ArgKindOf (f :: k -> l) = k

-- | The intersection of two 'TypeRepMap's using a combining function.
intersectionWith :: (forall x. f x -> f x -> f x) -> TypeRepMap f -> TypeRepMap f -> TypeRepMap f
intersectionWith f m1 m2 = TM.fromTriples
                         $ toTripleList
                         $ Map.intersectionWith combine
                                                (fromTripleList $ TM.toTriples m1)
                                                (fromTripleList $ TM.toTriples m2)
  where
    combine :: (Any, Any) -> (Any, Any) -> (Any, Any)
    combine (av, ak) (bv, _) = (TM.toAny $ f (TM.fromAny av) (TM.fromAny bv), ak)

    fromTripleList :: Ord a => [(a, b, c)] -> Map.Map a (b, c)
    fromTripleList = Map.fromList . map (\(a, b, c) -> (a, (b, c)))

    toTripleList :: Map.Map a (b, c) -> [(a, b, c)]
    toTripleList = map (\(a, (b, c)) -> (a, b, c)) . Map.toList
{-# INLINE intersectionWith #-}

-- | The (left-biased) intersection of two 'TypeRepMap's. It prefers the first map when
-- duplicate keys are encountered, i.e. @'intersect' == 'intersectionWith' const@.
intersection :: TypeRepMap f -> TypeRepMap f -> TypeRepMap f
intersection = intersectionWith const
{-# INLINE intersection #-}

-- | Fold all values a la monoid
mfold :: Monoid a => (forall x. f x -> a) -> TypeRepMap f -> a
mfold f = foldMap f (<>) mempty
{-# INLINE mfold #-}

-- | Fold all values by the given aggregation specification
foldMap :: (forall x. f x -> a) -> (a -> a -> a) -> a -> TypeRepMap f -> a
foldMap f g a m = foldr (g . (\(_, v, _) -> f (TM.fromAny v))) a (TM.toTriples m)
{-# INLINE foldMap #-}

-- | Return the list of keys by wrapping them with a user-provided function.
keysWith :: (forall (a :: ArgKindOf f). TypeRep a -> r) -> TypeRepMap f -> [r]
keysWith f TM.TypeRepMap{..} = f . TM.anyToTypeRep <$> toList trKeys
{-# INLINE keysWith #-}

-- | Return the list of key-value pairs by wrapping them with a user-provided function.
toListWith :: forall f r . (forall (a :: ArgKindOf f) . Typeable a => f a -> r) -> TypeRepMap f -> [r]
toListWith f = map toF . TM.toTriples
  where
    withTypeRep :: forall a. TypeRep a -> f a -> r
    withTypeRep tr an = withTypeable tr $ f an
    toF (_, an, k) = withTypeRep (unsafeCoerce k) (TM.fromAny an)
{-# INLINE toListWith #-}

instance (forall (a :: k). Typeable a => Hashable (f a)) => Hashable (TypeRepMap f) where
  hashWithSalt salt m = hashes salt
    where
      hashes = foldr (.) (`hashWithSalt` "TypeRepMap") (toListWith entryHash m)
      entryHash :: forall (a :: ArgKindOf f) . (Typeable a, Hashable (f a)) => f a -> (Int -> Int)
      entryHash k = \salt -> salt `hashWithSalt` (show (typeRep @a), k)

-- tm1 :: TypeRepMap (Map.Map Int)
-- tm1 = TM.one (Map.singleton (1 :: Int) (10 :: Int))
-- tm2 :: TypeRepMap (Map.Map Int)
-- tm2 = TM.insert (Map.insert 10 "456" $ Map.singleton (1 :: Int) "123") $ TM.one (Map.singleton (2 :: Int) (10 :: Int))
