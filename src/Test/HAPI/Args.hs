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
import qualified Data.Serialize as S
import Foreign (Ptr, nullPtr)

type Args          a = NP I          a
type Attributes c  a = NP (Attribute c) a
type DirAttributes c a = NP (DirectAttribute c) a
type ArgPattern    a = NP (K String) a

pattern (::*) :: x -> Args xs -> Args (x : xs)
pattern a ::* b = I a :* b
{-# COMPLETE (::*) :: NP #-}
infixr 2 ::*


data Attribute c a where
  Direct    :: forall a c. (Fuzzable a, Typeable c) => DirectAttribute c a -> Attribute c a
  Exogenous :: forall c a. (Fuzzable a, c a, Typeable c) => ExogenousAttribute c a -> Attribute c a


data DACompOp
  = DGt
  | DGte
  | DLt
  | DLte
  deriving (Eq, Ord, Show, Enum, Bounded)

data DirectAttribute c a where
  Value   :: (c a) => a -> DirectAttribute c a
  Get     :: (c a) => PKey a -> DirectAttribute c a
  -- Basic Calculations, easy translatable into C (or other language) code
  DNot    :: (c Bool) => DirectAttribute c Bool -> DirectAttribute c Bool
  DAnd    :: (c Bool) => DirectAttribute c Bool -> DirectAttribute c Bool -> DirectAttribute c Bool
  DOr     :: (c Bool) => DirectAttribute c Bool -> DirectAttribute c Bool -> DirectAttribute c Bool
  DPlus   :: (c a, Num a) => DirectAttribute c a -> DirectAttribute c a -> DirectAttribute c a
  DMinus  :: (c a, Num a) => DirectAttribute c a -> DirectAttribute c a -> DirectAttribute c a
  DMul    :: (c a, Num a) => DirectAttribute c a -> DirectAttribute c a -> DirectAttribute c a
  DDiv    :: (c a, Num a, Integral a) => DirectAttribute c a -> DirectAttribute c a -> DirectAttribute c a
  DFDiv   :: (c a, Num a, Fractional a) => DirectAttribute c a -> DirectAttribute c a -> DirectAttribute c a
  DNeg    :: (c a, Num a) => DirectAttribute c a -> DirectAttribute c a
  DCmp    :: (c a, Fuzzable a, Ord a) => DACompOp -> DirectAttribute c a -> DirectAttribute c a -> DirectAttribute c Bool
  DEq     :: (c a, Fuzzable a, Eq  a) => Bool     -> DirectAttribute c a -> DirectAttribute c a -> DirectAttribute c Bool

  DCastInt :: (c a, c b, Fuzzable a, Fuzzable b, Integral a, Integral b)
           => DirectAttribute c a -> DirectAttribute c b

  DNullptr :: DirectAttribute c (Ptr a)

data ExogenousAttribute c a where
  Anything :: (Typeable c, c a)
           => ExogenousAttribute c a
  IntRange :: (Typeable c, c Int)
           => Int -> Int -> ExogenousAttribute c Int
  Range    :: (Typeable c, Enum a, Ord a, c a)
           => a -> a -> ExogenousAttribute c a

-- Smart constructor

value :: (c a, Fuzzable a, Typeable c) => a -> Attribute c a
value = Direct . Value

var :: (c a, Fuzzable a, Typeable c) => PKey a -> Attribute c a
var = Direct . Get

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


evalDirect :: Typeable a => PState -> DirectAttribute c a -> a
evalDirect s (Value v) = v
evalDirect s (DNot  d) = not (evalDirect s d)
evalDirect s (Get   k) = fromMaybe (fatalError 'evalDirect FATAL_ERROR $ printf "Cannot find %s in the scope" (show k))
                       $ lookUp k s
evalDirect s (DAnd da1 da2)   = evalDirect s da1 && evalDirect s da2
evalDirect s (DOr  da1 da2)   = evalDirect s da1 || evalDirect s da2
evalDirect s (DPlus da1 da2)  = evalDirect s da1 + evalDirect s da2
evalDirect s (DMinus da1 da2) = evalDirect s da1 - evalDirect s da2
evalDirect s (DMul da1 da2)   = evalDirect s da1 * evalDirect s da2
evalDirect s (DDiv da1 da2)   = evalDirect s da1 `quot` evalDirect s da2
evalDirect s (DFDiv da1 da2)  = evalDirect s da1 / evalDirect s da2
evalDirect s (DNeg  da')      = negate $ evalDirect s da'
evalDirect s (DCmp c da1 da2) = evalDirect s da1 <=> evalDirect s da2
  where
    (<=>) = case c of
      DGt  -> (>)
      DGte -> (>=)
      DLt  -> (<)
      DLte -> (<=)
evalDirect s (DEq b da1 da2) = (evalDirect s da1 == evalDirect s da2) == b
evalDirect s (DCastInt a)    = fromIntegral (evalDirect s a)
evalDirect s DNullptr        = nullPtr

evalDirects :: (All Fuzzable p) => PState -> DirAttributes c p -> Args p
evalDirects _ Nil       = Nil
evalDirects s (a :* as) = I (evalDirect s a) :* evalDirects s as

simplifyDirect :: Typeable a => PState -> DirectAttribute c a -> DirectAttribute c a
simplifyDirect s (Value v)        = Value v
simplifyDirect s (DNot  d)        = DNot   (simplifyDirect s d)
simplifyDirect s (Get   k)        = maybe  (Get k) Value (lookUp k s)
simplifyDirect s (DAnd da1 da2)   = DAnd   (simplifyDirect s da1) (simplifyDirect s da2)
simplifyDirect s (DOr  da1 da2)   = DOr    (simplifyDirect s da1) (simplifyDirect s da2)
simplifyDirect s (DPlus da1 da2)  = DPlus  (simplifyDirect s da1) (simplifyDirect s da2)
simplifyDirect s (DMinus da1 da2) = DMinus (simplifyDirect s da1) (simplifyDirect s da2)
simplifyDirect s (DMul da1 da2)   = DMul   (simplifyDirect s da1) (simplifyDirect s da2)
simplifyDirect s (DDiv da1 da2)   = DDiv   (simplifyDirect s da1) (simplifyDirect s da2)
simplifyDirect s (DFDiv da1 da2)  = DFDiv  (simplifyDirect s da1) (simplifyDirect s da2)
simplifyDirect s (DNeg  da')      = DNeg   (simplifyDirect s da')
simplifyDirect s (DCmp c da1 da2) = DCmp c (simplifyDirect s da1) (simplifyDirect s da2)
simplifyDirect s (DEq b da1 da2)  = DEq  b (simplifyDirect s da1) (simplifyDirect s da2)
simplifyDirect s (DCastInt a)     = DCastInt (simplifyDirect s a)
simplifyDirect s DNullptr         = DNullptr

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

dirAttrs2Pat :: forall c p. All Fuzzable p => DirAttributes c p -> ArgPattern p
dirAttrs2Pat = hcmap (Proxy @Fuzzable) (K . show)

eqAttributes :: (Typeable c, All Fuzzable p) => Attributes c p -> Attributes c p -> Bool
eqAttributes Nil       Nil       = True
eqAttributes (a :* as) (b :* bs) = a == b && eqAttributes as bs

eqAttributes' :: (All Fuzzable p, Typeable p, Typeable c, Typeable c1) => Attributes c p -> Attributes c1 p -> Bool
eqAttributes' a b = case testEquality (typeOf a) (typeOf b) of
  Nothing    -> False
  Just proof -> castWith proof a `eqAttributes` b

instance Show a => Show (DirectAttribute c a) where
  show (Value a)        = show a
  show (Get pk)         = getPKeyID pk
  show (DNot da')       = "!" <> show da'
  show (DAnd da1 da2)   = printf "(%s && %s)" (show da1) (show da2)
  show (DOr  da1 da2)   = printf "(%s || %s)" (show da1) (show da2)
  show (DPlus da1 da2)  = printf "(%s + %s)" (show da1) (show da2)
  show (DMinus da1 da2) = printf "(%s - %s)" (show da1) (show da2)
  show (DMul da1 da2)   = printf "(%s * %s)" (show da1) (show da2)
  show (DDiv da1 da2)   = printf "(%s // %s)" (show da1) (show da2)
  show (DFDiv da1 da2)  = printf "(%s / %s)" (show da1) (show da2)
  show (DNeg da')       = printf "-%s" (show da')
  show (DCmp c da1 da2) = printf "(%s %s %s)" (showCmp c) (show da1) (show da2)
    where
      showCmp DGt  = ">"
      showCmp DGte = ">="
      showCmp DLt  = "<"
      showCmp DLte = "<="
  show (DEq b da1 da2)  = printf "(%s %s %s)" (show da1) (if b then "==" else "/=") (show da2)
  show (DCastInt a)     = printf "(%s as int)" (show a)
  show DNullptr         = printf "NULL"


instance Show a => Show (ExogenousAttribute c a) where
  show Anything = "Anything"
  show (IntRange n i) = "[" <> show n <> ".." <> show i <> "]"
  show (Range a a') = "[" <> show a <> ".." <> show a' <> "]"
instance Show a => Show (Attribute c a) where
  show (Direct    d) = show d
  show (Exogenous d) = show d

instance (Typeable c, Eq a) => Eq (DirectAttribute c a) where
  (Value a)        == (Value a')          = a == a'
  (Get a)          == (Get a')            = a == a'
  (DNot a)         == (DNot a')           = a == a'
  (DAnd a1 a2)     == (DAnd a1' a2')      = a1 == a1' && a2 == a2'
  (DOr  a1 a2)     == (DOr  a1' a2')      = a1 == a1' && a2 == a2'
  (DPlus a1 a2)    == (DPlus a1' a2')     = a1 == a1' && a2 == a2'
  (DMinus a1 a2)   == (DMinus a1' a2')    = a1 == a1' && a2 == a2'
  (DMul a1 a2)     == (DMul a1' a2')      = a1 == a1' && a2 == a2'
  (DDiv a1 a2)     == (DDiv a1' a2')      = a1 == a1' && a2 == a2'
  (DNeg da)        == (DNeg da')          = da == da'
  (DCmp c a1 a2)   == (DCmp c' a1' a2')   = c == c' && a1 `repEq` a1' && a2 `repEq` a2'
  (DEq  b a1 a2)   == (DEq  b' a1' a2')   = b == b' && a1 `repEq` a1' && a2 `repEq` a2'
  (DCastInt a)     == (DCastInt b)        = a `repEq` b
  DNullptr         == DNullptr            = True
  _ == _ = False


deriving instance Eq a => Eq (ExogenousAttribute c a)
instance (Typeable c, Eq a) => Eq (Attribute c a) where
  Direct    d1 == Direct d2    = d1 == d2
  Exogenous e1 == Exogenous e2 = e1 == e2
  _ == _ = False

instance Hashable a => Hashable (DirectAttribute c a) where
  hashWithSalt salt = \case
    Value a        -> salt `hashWithSalt` "value" `hashWithSalt` a
    Get   pk       -> salt `hashWithSalt` "get"   `hashWithSalt` pk
    DNot  d        -> salt `hashWithSalt` "not"   `hashWithSalt` d
    DAnd da1 da2   -> salt `hashWithSalt` "and"   `hashWithSalt` da1 `hashWithSalt` da2
    DOr  da1 da2   -> salt `hashWithSalt` "or"    `hashWithSalt` da1 `hashWithSalt` da2
    DPlus da1 da2  -> salt `hashWithSalt` "plus"  `hashWithSalt` da1 `hashWithSalt` da2
    DMinus da1 da2 -> salt `hashWithSalt` "min"   `hashWithSalt` da1 `hashWithSalt` da2
    DMul da1 da2   -> salt `hashWithSalt` "mul"   `hashWithSalt` da1 `hashWithSalt` da2
    DDiv da1 da2   -> salt `hashWithSalt` "div"   `hashWithSalt` da1 `hashWithSalt` da2
    DFDiv da1 da2  -> salt `hashWithSalt` "fdiv"  `hashWithSalt` da1 `hashWithSalt` da2
    DNeg  da'      -> salt `hashWithSalt` "neg"   `hashWithSalt` da'
    DCmp c da1 da2 -> salt `hashWithSalt` "cmp"   `hashWithSalt` fromEnum c `hashWithSalt` da1 `hashWithSalt` da2
    DEq  b da1 da2 -> salt `hashWithSalt` "eq"    `hashWithSalt` b `hashWithSalt` da1 `hashWithSalt` da2
    DCastInt x     -> salt `hashWithSalt` "casti" `hashWithSalt` x
    DNullptr       -> salt `hashWithSalt` "null"

instance Hashable a => Hashable (ExogenousAttribute c a) where
  hashWithSalt salt = \case
    Anything     -> salt `hashWithSalt` "any"
    IntRange n i -> salt `hashWithSalt` "irange" `hashWithSalt` n `hashWithSalt` i
    Range a a'   -> salt `hashWithSalt` "range" `hashWithSalt` a `hashWithSalt` a'

instance Hashable a => Hashable (Attribute c a) where
  hashWithSalt salt = \case
    Direct d     -> salt `hashWithSalt` "dir" `hashWithSalt` d
    Exogenous d  -> salt `hashWithSalt` "exo" `hashWithSalt` d

    -- AnyOf ats    -> salt `hashWithSalt` "anyof" `hashWithSalt` ats

instance (All Fuzzable p) => Hashable (NP (Attribute c) p) where
  hashWithSalt salt Nil       = salt `hashWithSalt` "Nil"
  hashWithSalt salt (a :* as) = salt `hashWithSalt` ":*" `hashWithSalt` a `hashWithSalt` as
