{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Test.HAPI.AASTG.Effect.Trav where
import Data.Kind (Type)

data Trav (m :: Type -> Type) a where
