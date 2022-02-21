{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Test.HAPI.PState where
import Test.HAPI.DataType (TypeSpec, TyIn)
import Data.Kind (Type)
import Control.Algebra (Has, type (:+:))
import Control.Effect.State (State)
import Control.Carrier.Fresh.Church (Fresh)
import Control.Effect.Labelled (Labelled)

data Ref t

-- class PState (state :: TypeSpec -> Type) where
--   record :: (TyIn t types) => t -> state types -> (state types, Ref t)
--   ref    :: (TyIn t types) => Ref t -> state types -> t
