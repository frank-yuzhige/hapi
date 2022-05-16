{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Test.HAPI.Constraint where
import Data.Kind ( Type, Constraint )
import Data.Constraint
    ( (\\),
      mapDict,
      refl,
      unmapDict,
      type (:-)(..),
      Dict(..) )

type Constraint1 = Type -> Constraint

-- | Unary Constraint Conjunction: @(f :<>: g) a@ is the same as @f a@ and @g a@
class (f t, g t) => (f :<>: g) t where

instance (f t, g t) => (f :<>: g) t where

infixr 4 :<>:

-- | Unary Constraint a la carte, @projEntailment@ provides a "witness" to the entailment relation that @sup a@ entails @sub a@
class (sup :: Constraint1) :>>>: (sub :: Constraint1) where
  projEntailment :: sup a :- sub a

instance f :>>>: f where
  projEntailment = refl
  {-# INLINE projEntailment #-}

instance {-# OVERLAPPABLE #-}
         (f :<>: r) :>>>: f where
  projEntailment = Sub Dict
  {-# INLINE projEntailment #-}

instance {-# OVERLAPPABLE #-}
         (r :>>>: f)
      => (l :<>: r) :>>>: f where
  projEntailment = unmapDict $ \d -> mapDict (projEntailment @r @f) (Dict \\ d)
  {-# INLINE projEntailment #-}

instance {-# OVERLAPPABLE #-}
         ((l1 :<>: l2 :<>: l3) :>>>: f)
      => ((l1 :<>: l2) :<>: l3) :>>>: f where
  projEntailment = unmapDict $ \d -> mapDict (projEntailment @(l1 :<>: l2 :<>: l3) @f) (Dict \\ d)
  {-# INLINE projEntailment #-}

-- | Cast a witness of a Constraint1 satisfies a type, by applying an entailment via projEntailment.
castC :: forall g f a. (f :>>>: g) => Dict (f a) -> Dict (g a)
castC = mapDict projEntailment

type family CMembers (sub :: Constraint1) (sup :: Constraint1) :: Constraint where
  CMembers (f :<>: g) s = (CMembers f s, CMembers g s)
  CMembers f          s = s :>>>: f
