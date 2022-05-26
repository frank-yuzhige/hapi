{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstraintKinds #-}

module Test.HAPI.Args where
import Data.HList (HList (HCons, HNil), HBuild', HList2List (hList2List), Proxy (Proxy))
import GHC.Base (Nat)
import Data.Kind (Type, Constraint)
import GHC.TypeLits (type (-), type (+))
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Quote (QuasiQuoter (quoteDec, quotePat, quoteType, quoteExp, QuasiQuoter))
import Data.HList.HList (hBuild)
import Data.HList.CommonMain (hEnd)
import Data.SOP (NP (Nil, (:*)), All, Compose, I (I), K (K), hcmap, unI, Top)
import Data.List (intercalate)
import Language.Haskell.Meta (parseExp)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.PState (PKey (..), PState (PState), PStateSupports (lookUp))
import Data.Data (Typeable)
import Data.Type.Equality (testEquality, castWith)
import Type.Reflection (typeOf)
import Data.Hashable (Hashable (hashWithSalt))
import Data.Maybe (fromMaybe)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR))
import Text.Printf (printf)

type Args          a = NP I          a
type Attributes c  a = NP (Attribute c) a
type DirAttributes a = NP DirectAttribute a
type ArgPattern    a = NP (K String) a

pattern (::*) :: x -> Args xs -> Args (x : xs)
pattern a ::* b = I a :* b
{-# COMPLETE (::*) :: NP #-}
infixr 2 ::*


data Attribute c a where
  Direct    :: forall a c. (Fuzzable a) => DirectAttribute a -> Attribute c a
  Exogenous :: forall c a. (Fuzzable a, c a, Typeable c) => ExogenousAttribute c a -> Attribute c a
  -- AnyOf    :: (Fuzzable a) => [Attribute a] -> Attribute a


data DirectAttribute a where
  Value :: a -> DirectAttribute a
  Get   :: PKey a -> DirectAttribute a
  DNot  :: DirectAttribute Bool -> DirectAttribute Bool

data ExogenousAttribute c a where
  Anything :: (Typeable c, c a)   => ExogenousAttribute c a
  IntRange :: (Typeable c, c Int) => Int -> Int -> ExogenousAttribute c Int
  Range    :: (Typeable c, Enum a, Ord a, c a)
           => a -> a -> ExogenousAttribute c a

-- Smart constructor

value :: (Fuzzable a) => a -> Attribute c a
value = Direct . Value

getVar :: (Fuzzable a) => PKey a -> Attribute c a
getVar = Direct . Get

anything :: forall c a. (Fuzzable a, c a, Typeable c) => Attribute c a
anything = Exogenous @c Anything

range :: forall c a. (Fuzzable a, Enum a, Ord a, c a, Typeable c) => a -> a -> Attribute c a
range a b = Exogenous @c $ Range a b

irange :: forall c a. (Fuzzable Int, c Int, Typeable c) => Int -> Int -> Attribute c Int
irange a b = Exogenous @c $ IntRange a b

args2Pat :: forall p. All Fuzzable p => Args p -> ArgPattern p
args2Pat = hcmap (Proxy @Fuzzable) (K . show . unI)

args :: QuasiQuoter
args = QuasiQuoter {
    quoteExp = exp . words,
    quoteType = err,
    quotePat = pat . words,
    quoteDec = err
  }
  where
    err = error "args is for pattern"
    pat []       = [p|Nil|]
    pat (x : xs) = [p|I $(return (if x == "_" then WildP else VarP (mkName x))) :* $(pat xs)|]
    exp []       = [e|Nil|]
    exp (x : xs) = case parseExp x of
      Left err -> fail err
      Right r  -> [e|I $(return r) :* $(exp xs)|]


evalDirect :: Typeable a => PState -> DirectAttribute a -> a
evalDirect s (Value v) = v
evalDirect s (DNot  d) = not (evalDirect s d)
evalDirect s (Get   k) = fromMaybe (fatalError 'evalDirect FATAL_ERROR $ printf "Cannot find %s in the scope" (show k))
                       $ lookUp k s

evalDirects :: (All Fuzzable p) => PState -> DirAttributes p -> Args p
evalDirects _ Nil       = Nil
evalDirects s (a :* as) = I (evalDirect s a) :* evalDirects s as

-- | Check if the provided value satisfies the attribute
validate :: Attribute c a -> a -> Bool
validate attr a = case attr of
  Exogenous (IntRange l r) -> l <= a && a <= r
  Exogenous (Range    l r) -> l <= a && a <= r
  _                        -> True

attributesEq :: forall a b c c1.
              ( Typeable a
              , Typeable b
              , Typeable c
              , Typeable c1
              , All (Compose Eq (Attribute c)) a
              , All (Compose Eq (Attribute c)) b
              , All (Compose Eq (Attribute c1)) a
              , All (Compose Eq (Attribute c1)) b
              )
             => Attributes c a -> Attributes c1 b -> Bool
attributesEq a b = case testEquality (typeOf a) (typeOf b) of
  Nothing    -> False
  Just proof -> castWith proof a == b

repEq :: forall f a b. (Typeable (f a), Typeable (f b), Eq (f b)) => f a -> f b -> Bool
repEq a b = case testEquality (typeOf a) (typeOf b) of
  Nothing    -> False
  Just proof -> castWith proof a == b

attrs2Pat :: forall p c. All Fuzzable p => Attributes c p -> ArgPattern p
attrs2Pat = hcmap (Proxy @Fuzzable) (K . show)

dirAttrs2Pat :: forall p. All Fuzzable p => DirAttributes p -> ArgPattern p
dirAttrs2Pat = hcmap (Proxy @Fuzzable) (K . show)

eqAttributes :: (All Fuzzable p) => Attributes c p -> Attributes c p -> Bool
eqAttributes Nil       Nil       = True
eqAttributes (a :* as) (b :* bs) = a == b && eqAttributes as bs

eqAttributes' :: (All Fuzzable p, Typeable p, Typeable c, Typeable c1) => Attributes c p -> Attributes c1 p -> Bool
eqAttributes' a b = case testEquality (typeOf a) (typeOf b) of
  Nothing    -> False
  Just proof -> castWith proof a `eqAttributes` b
-- Hoist
-- attrInt2Bool :: (Integral i, Fuzzable i) => Attribute i -> Attribute Bool
-- attrInt2Bool (Direct (Value i))   = value (i /= 0)
-- attrInt2Bool (Exogenous Anything) = Exogenous Anything
-- attrInt2Bool (Exogenous (IntRange l r))
--   | l == 0 && r == 0 = value False
--   | l <= 0 && 0 <= r = Exogenous $ Range False True
--   | otherwise        = value True
-- attrInt2Bool (Exogenous (Range l r))
--   | l == 0 && r == 0 = value False
--   | l <= 0 && 0 <= r = Exogenous $ Range False True
--   | otherwise        = value True
-- attrInt2Bool (Direct (Get pk))       = getVar (PKey $ getPKeyID pk)
-- attrInt2Bool (AnyOf ats)    = AnyOf (map attrInt2Bool ats)

instance Show a => Show (DirectAttribute a) where
  show (Value a)  = show a
  show (Get   pk) = getPKeyID pk
  show (DNot  v)  = "!" <> show v


instance Show a => Show (ExogenousAttribute c a) where
  show Anything = "Anything"
  show (IntRange n i) = "[" <> show n <> ".." <> show i <> "]"
  show (Range a a') = "[" <> show a <> ".." <> show a' <> "]"
instance Show a => Show (Attribute c a) where
  show (Direct    d) = show d
  show (Exogenous d) = show d

deriving instance Eq a => Eq (DirectAttribute a)
deriving instance Eq a => Eq (ExogenousAttribute c a)
instance Eq a => Eq (Attribute c a) where
  Direct    d1 == Direct d2    = d1 == d2
  Exogenous e1 == Exogenous e2 = case testEquality (typeOf e1) (typeOf e2) of
    Nothing    -> False
    Just proof -> castWith proof e1 == e2
  _ == _ = False

instance Hashable a => Hashable (DirectAttribute a) where
  hashWithSalt salt = \case
    Value a  -> salt `hashWithSalt` "value" `hashWithSalt` a
    Get   pk -> salt `hashWithSalt` "get" `hashWithSalt` pk
    DNot  d  -> salt `hashWithSalt` "not" `hashWithSalt` d

instance Hashable a => Hashable (ExogenousAttribute c a) where
  hashWithSalt salt = \case
    Anything     -> salt `hashWithSalt` "any"
    IntRange n i -> salt `hashWithSalt` "irange" `hashWithSalt` n `hashWithSalt` i
    Range a a'   -> salt `hashWithSalt` "range" `hashWithSalt` a `hashWithSalt` a
instance Hashable a => Hashable (Attribute c a) where
  hashWithSalt salt = \case
    Direct d     -> salt `hashWithSalt` "dir" `hashWithSalt` d
    Exogenous d  -> salt `hashWithSalt` "exo" `hashWithSalt` d

    -- AnyOf ats    -> salt `hashWithSalt` "anyof" `hashWithSalt` ats

instance (All Fuzzable p) => Hashable (NP (Attribute c) p) where
  hashWithSalt salt Nil       = salt `hashWithSalt` "Nil"
  hashWithSalt salt (a :* as) = salt `hashWithSalt` ":*" `hashWithSalt` a `hashWithSalt` as
