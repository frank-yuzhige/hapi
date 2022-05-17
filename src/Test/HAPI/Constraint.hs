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
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.Constraint where
import Data.Kind ( Type, Constraint )
import Data.Constraint
    ( (\\),
      mapDict,
      refl,
      unmapDict,
      type (:-)(..),
      Dict(..), (&&&), trans )
import Data.Graph.Inductive.Example (a)

type Constraint1 = Type -> Constraint

-- | Unary Constraint Conjunction: @(f :<>: g) a@ is the same as @f a@ and @g a@
class (f t, g t) => (f :<>: g) t where

instance (f t, g t) => (f :<>: g) t where

infixr 4 :<>:

-- | Unary Constraint a la carte, @projEntailment@ provides a "witness" to the entailment relation that @sup a@ entails @sub a@
class (sup :: Constraint1) :>>>: (sub :: Constraint1) where
  projEntailment :: sup a :- sub a

instance {-# OVERLAPPABLE #-} f :>>>: f where
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

-- instance {-# OVERLAPPABLE #-}
--          ( f :>>>: l1
--          , f :>>>: l2)
--       => (f :>>>: (l1 :<>: l2)) where
--   projEntailment :: forall a. f a :- (:<>:) l1 l2 a
--   projEntailment = Sub $ Dict \\ f1 \\ f2
--     where
--       f1 = projEntailment @f @l1 @a
--       f2 = projEntailment @f @l2 @a

-- | Cast a witness of a Constraint1 satisfies a type, by applying an entailment via projEntailment.
castC :: forall g f a. (f :>>>: g) => Dict (f a) -> Dict (g a)
castC = mapDict projEntailment

transC :: forall f g h a. (f :>>>: g, g :>>>: h) => f a :- h a
transC = trans (projEntailment @g @h) (projEntailment @f @g)

productC :: forall s g h f a. (f :>>>: g, f :>>>: h, s ~ (g :<>: h)) => f a :- (g :<>: h) a
productC = Sub $ Dict \\ f1 \\ f2
  where
    f1 = projEntailment @f @g @a
    f2 = projEntailment @f @h @a

dikt :: forall c a. (c a) => Dict (c a)
dikt = Dict

-- castL :: forall f l1 a l2. (f :>>>: (l1 :<>: l2)) => Dict (f a) -> Dict (l1 a)
-- castL = mapDict projEntailment

-- castR ::  forall f l2 a l1. (CMembers (l1 :<>: l2) f) => Dict (f a) -> Dict (l2 a)
-- castR = _

type family CMembers (sub :: Constraint1) (sup :: Constraint1) :: Constraint where
  CMembers (f :<>: g) s = (CMembers f s, CMembers g s)
  CMembers f          s = s :>>>: f
