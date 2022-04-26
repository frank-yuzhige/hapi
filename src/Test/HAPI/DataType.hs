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
import Test.HAPI.Common (Fuzzable)



type family TySpec (c :: Type -> Constraint) (ts :: [Type]) :: Constraint where
  TySpec c '[]      = ()
  TySpec c (t : ts) = (c t, TySpec c ts)


type BasicTypes = '[Int, Char, Bool, String]

type BasicSpec c = (TySpec c BasicTypes, TySpec Fuzzable BasicTypes)
