{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Test.HAPI.Args where
import Data.HList (HList (HCons, HNil), HBuild', HList2List (hList2List))
import GHC.Base (Nat)
import Data.Kind (Type)
import GHC.TypeLits (type (-), type (+))
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Quote (QuasiQuoter (quoteDec, quotePat, quoteType, quoteExp, QuasiQuoter))
import Data.HList.HList (hBuild)
import Data.HList.CommonMain (hEnd)
import Data.SOP (NP (Nil, (:*)), All, Compose)
import Data.Functor.Identity (Identity (Identity))
import Data.List (intercalate)
import Language.Haskell.Meta (parseExp)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.PState (PKey (getPKeyID))
import Data.Data (Typeable)
import Data.Type.Equality (testEquality, castWith)
import Type.Reflection (typeOf)
import Data.Hashable (Hashable (hashWithSalt))

type Args       a = NP Identity  a
type Attributes a = NP Attribute a

pattern (::*) :: x -> Args xs -> Args (x : xs)
pattern a ::* b = Identity a :* b
{-# COMPLETE (::*) :: NP #-}
infixr 2 ::*


data Attribute a where
  Value    :: (Fuzzable a) => a -> Attribute a
  Anything :: (Fuzzable a) => Attribute a
  IntRange :: Int -> Int -> Attribute Int
  Range    :: (Fuzzable a, Ord a, Enum a)
           => a -> a -> Attribute a
  Get      :: (Fuzzable a) => PKey a -> Attribute a
  AnyOf    :: (Fuzzable a) => [Attribute a] -> Attribute a


noArgs :: Args '[]
noArgs = Nil

showArgs :: forall p. All Fuzzable p => Args p -> String
showArgs args = "(" <> intercalate ", " (go args) <> ")"
  where
    go :: forall p. All Fuzzable p => Args p -> [String]
    go Nil                = []
    go (Identity a :* as) = show a : go as

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
    pat (x : xs) = [p|Identity $(return (if x == "_" then WildP else VarP (mkName x))) :* $(pat xs)|]
    exp []       = [e|Nil|]
    exp (x : xs) = case parseExp x of
      Left err -> fail err
      Right r  -> [e|Identity $(return r) :* $(exp xs)|]


-- | Check if the provided value satisfies the attribute
validate :: Attribute a -> a -> Bool
validate attr a = case attr of
  IntRange l r -> l <= a && a <= r
  Range    l r -> l <= a && a <= r
  _            -> True

attributesEq :: forall a b. (Typeable a, Typeable b, All (Compose Eq Attribute) a, All (Compose Eq Attribute) b) => Attributes a -> Attributes b -> Bool
attributesEq a b = case testEquality (typeOf a) (typeOf b) of
  Nothing    -> False
  Just proof -> castWith proof a == b

repEq :: forall f a b. (Typeable (f a), Typeable (f b), Eq (f b)) => f a -> f b -> Bool
repEq a b = case testEquality (typeOf a) (typeOf b) of
  Nothing    -> False
  Just proof -> castWith proof a == b

showAttributes :: (All Fuzzable p) => Attributes p -> [String]
showAttributes Nil       = []
showAttributes (a :* as) = show a : showAttributes as

eqAttributes :: (All Fuzzable p) => Attributes p -> Attributes p -> Bool
eqAttributes Nil       Nil       = True
eqAttributes (a :* as) (b :* bs) = a == b && eqAttributes as bs

instance Show a => Show (Attribute a) where
  show (Value a) = show a
  show Anything = "Anything"
  show (IntRange n i) = "[" <> show n <> ".." <> show i <> "]"
  show (Range a a') = "[" <> show a <> ".." <> show a' <> "]"
  show (Get pk) = getPKeyID pk
  show (AnyOf ats) = "Any of " <> show ats

deriving instance Eq a => Eq (Attribute a)

instance Hashable a => Hashable (Attribute a) where
  hashWithSalt salt = \case
    Value a      -> salt `hashWithSalt` "value" `hashWithSalt` a
    Anything     -> salt `hashWithSalt` "any"
    IntRange n i -> salt `hashWithSalt` "irange" `hashWithSalt` n `hashWithSalt` i
    Range a a'   -> salt `hashWithSalt` "range" `hashWithSalt` a `hashWithSalt` a
    Get pk       -> salt `hashWithSalt` "get" `hashWithSalt` pk
    AnyOf ats    -> salt `hashWithSalt` "anyof" `hashWithSalt` ats

instance (All Fuzzable p) => Hashable (NP Attribute p) where
  hashWithSalt salt Nil       = salt `hashWithSalt` "Nil"
  hashWithSalt salt (a :* as) = salt `hashWithSalt` a `hashWithSalt` as
