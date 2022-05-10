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
import Data.Constraint (Constraint, type (:-) (Sub), Dict (Dict), HasDict (evidence), type (:=>))
import Data.Kind (Type)
import Data.Data (Proxy (Proxy), TyCon)
import Data.Constraint.Forall (Forall)
import Test.HAPI.Common (Fuzzable)



type family TySpec (c :: Type -> Constraint) (ts :: [Type]) :: Constraint where
  TySpec c '[]      = ()
  TySpec c (t : ts) = (c t, TySpec c ts)


type BasicTypes = '[Int, Char, Bool, String]

class TyIn (spec :: [Type]) t
instance TyIn (t : ts) t
instance TyIn ts t => TyIn (t' : ts) t

class (TySpec c spec) => Spec (spec :: [Type]) (c :: Type -> Constraint) t where
  spec :: Dict (c t)

instance {-# OVERLAPPABLE #-}
         (TySpec c ts, c t)
      => Spec (t : ts) c t where
  spec = Dict @(c t)

instance {-# OVERLAPPABLE #-}
         ( Spec ts c t
         , c t')
      => Spec (t' : ts) c t where
  spec = spec @ts @c @t

-- instance {-# OVERLAPPABLE #-}
--          ( Spec ts c t
--          , c (m t))
--       => Spec ts c (m t) where

type BasicSpec c = (TySpec c BasicTypes, TySpec Fuzzable BasicTypes)


-- '[LLVMInt, LLVMDouble, LLVMFloat,]   --- Also want LLVMPtr LLVMInt, ...
-- some :: forall c a. () => Attribute a
-- some = apicall i j API (Value @LLVMInt 10 ::* Value @(LLVMPtr LLVMPtr LLVMChar) 0xdeadbeef)
