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
{-# LANGUAGE QuantifiedConstraints #-}

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

-- | Unary Constraint Product: @(f :<>: g) a@ is the same as @f a@ and @g a@
class (f t, g t) => (f :<>: g) t

instance (f t, g t) => (f :<>: g) t

infixr 4 :<>:

-- | Unary Constraint a la carte, @ucEntailment@ provides a "witness" to the entailment relation that @sup a@ entails @sub a@
class (sup :: Constraint1) :>>>: (sub :: Constraint1) where
  ucEntailment :: sup a :- sub a

instance {-# OVERLAPPABLE #-} f :>>>: f where
  ucEntailment = Sub Dict
  {-# INLINE ucEntailment #-}

instance {-# OVERLAPPABLE #-}
         (f :<>: r) :>>>: f where
  ucEntailment = Sub Dict
  {-# INLINE ucEntailment #-}

instance {-# OVERLAPPABLE #-}
         (r :>>>: f)
      => (l :<>: r) :>>>: f where
  ucEntailment = unmapDict $ \d -> mapDict (ucEntailment @r @f) (Dict \\ d)
  {-# INLINE ucEntailment #-}

instance {-# OVERLAPPABLE #-}
         ((l1 :<>: l2 :<>: l3) :>>>: f)
      => ((l1 :<>: l2) :<>: l3) :>>>: f where
  ucEntailment = unmapDict $ \d -> mapDict (ucEntailment @(l1 :<>: l2 :<>: l3) @f) (Dict \\ d)
  {-# INLINE ucEntailment #-}

-- | Cast a witness of a Constraint1 satisfies a type, by applying an entailment via ucEntailment.
castC :: forall g f a. (f :>>>: g) => Dict (f a) -> Dict (g a)
castC = mapDict ucEntailment

witnessC :: forall g f a. (f :>>>: g, f a) => Dict (g a)
witnessC = castC @g (Dict @(f a))

transC :: forall f g h a. (f :>>>: g, g :>>>: h) => f a :- h a
transC = trans (ucEntailment @g @h) (ucEntailment @f @g)

productC :: forall s g h f a. (f :>>>: g, f :>>>: h, s ~ (g :<>: h)) => f a :- (g :<>: h) a
productC = Sub $ Dict \\ f1 \\ f2
  where
    f1 = ucEntailment @f @g @a
    f2 = ucEntailment @f @h @a

-- castL = mapDict ucEntailment

-- castR ::  forall f l2 a l1. (CMembers (l1 :<>: l2) f) => Dict (f a) -> Dict (l2 a)
-- castR = _

type family CMembers (sub :: Constraint1) (sup :: Constraint1) :: Constraint where
  CMembers (f :<>: g) s = (CMembers f s, CMembers g s)
  CMembers f          s = s :>>>: f

class T (k :: Type)
instance T k
