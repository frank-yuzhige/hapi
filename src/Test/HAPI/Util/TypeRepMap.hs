{-# LANGUAGE RankNTypes #-}

-- | Extended internal API for 'TypeRepMap' and operations on it.
module Test.HAPI.Util.TypeRepMap where

import qualified Data.TypeRepMap as TM
import qualified Data.TypeRepMap.Internal as TM
import Data.TypeRepMap (TypeRepMap)
import qualified Data.Map.Strict as Map
import GHC.Exts (Any)
import Data.Functor.Identity (Identity(Identity))

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
mfold f = fold f (<>) mempty
{-# INLINE mfold #-}

-- | Fold all values by the given aggregation specification
fold :: (forall x. f x -> a) -> (a -> a -> a) -> a -> TypeRepMap f -> a
fold f g a m = foldr (g . (\(_, v, _) -> f (TM.fromAny v))) a (TM.toTriples m)
{-# INLINE fold #-}

-- | Degrade all values by the given degradation function
degrade :: (forall x. f x -> a) -> TypeRepMap f -> [a]
degrade f m = map (\(_, v, _) -> f (TM.fromAny v)) (TM.toTriples m)
{-# INLINE degrade #-}

-- tm1 :: TypeRepMap (Map.Map Int)
-- tm1 = TM.one (Map.singleton (1 :: Int) (10 :: Int))
-- tm2 :: TypeRepMap (Map.Map Int)
-- tm2 = TM.insert (Map.insert 10 "456" $ Map.singleton (1 :: Int) "123") $ TM.one (Map.singleton (2 :: Int) (10 :: Int))
