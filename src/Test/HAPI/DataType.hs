{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.DataType where
import Data.Constraint (Constraint, type (:-) (Sub), Dict (Dict), HasDict, type (:=>))
import Data.Kind (Type)
import Data.Data (Proxy (Proxy), TyCon)
import Data.Constraint.Forall (Forall)

type Ghost p = Constraint -> p

type family UnGhost (ghost :: Ghost p) :: p where
  UnGhost ghost = ghost ()

data TypeSpec (types :: [Type]) (constraints :: Type -> Constraint) = TypeSpec

type family GetSpecTypes (spec :: Type) :: [Type] where
  GetSpecTypes (TypeSpec types _) = types

type family GetSpecCons (spec :: Type) :: Type -> Constraint where
  GetSpecCons (TypeSpec _ cons) = cons


data (t :%: t') (ghost :: Constraint) = TL t | TR t'
infixr 5 :%:

newtype L t (ghost :: Constraint) = L t

class TyMember sub (sup :: [Type]) where

instance TyMember t '[t] where

instance {-# OVERLAPPABLE #-}
         TyMember t ts =>
         TyMember t (t' : ts) where
instance {-# OVERLAPPABLE #-}
         TyMember t (t : ts) where

class AllSat (c :: Type -> Constraint) (u :: [Type]) where
instance (c a, AllSat c b) =>  AllSat c (a : b)
instance AllSat c '[]

-- class (forall c. c t => AllSat c u) => TMember (t :: Type) (u :: [Type])
-- instance (forall c. c (u (() :: Constraint)) => c t, TyMember t u) => TMember t u

type family WFTypeSpec_ (c :: (Type -> Constraint)) (ts :: [Type]) :: Constraint where
  WFTypeSpec_ c '[t]     = (c t)
  WFTypeSpec_ c (t : ts) = (c t, WFTypeSpec_ c ts)

type family WFTypeSpec t :: Constraint where
  WFTypeSpec (TypeSpec ts cs) = WFTypeSpec_ cs ts

class (c t, d t) => CAnd (c :: Type -> Constraint) (d :: Type -> Constraint) t
instance (c t, d t) => CAnd c d t
type family (c :: Type -> Constraint) :&: (d :: Type -> Constraint) :: Type -> Constraint where
  c :&: d = CAnd c d
infixr 5 :&:

type family ConMember (sub :: Type -> Constraint) (sup :: Type -> Constraint) :: Constraint where
  ConMember c c = ()
  ConMember c (CAnd c  cs) = ()
  ConMember c (CAnd c' cs) = (ConMember c cs)

class (forall a. sup a => sub a) =>
  CMember (sub :: Type -> Constraint) (sup :: Type -> Constraint)
instance (forall a. sup a => sub a, ConMember sub sup) => CMember sub sup

-- type family SpecHasT spec t :: Constraint where
--   SpecHasT (TypeSpec ts cs) t = (WFTypeSpec_ cs ts, TMember t ts)

-- type family Spec spec t c :: Constraint where
--   Spec spec t c = (SpecHasT spec t, GetSpecCons spec ~ c)

-----------------------------
class CList (c :: [Type] -> Type) (ts :: [Type]) where
  type ReifiedCtx c :: Constraint

type TyIn t spec  = (TyMember t (GetSpecTypes spec), WFTypeSpec spec , (GetSpecCons spec) t)
type TyIn' t c ts = (TyMember t ts                 , WFTypeSpec_ c ts, c t)

x :: forall x xs. (TyIn' x Show xs, TyIn' x Read xs) => String -> String
x = show . read @x

useX :: String -> String
useX = x @Int @'[Int]

--------------------------------

type BasicTypes = '[Int, Char, Bool, String, Double]
type BasicSpec  = TypeSpec BasicTypes
