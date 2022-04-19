{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module Test.HAPI.Common where
import Data.Data (Typeable)
import Control.Algebra (Has, type (:+:))
import Data.Serialize (Serialize)
import Test.HAPI.VPtr (VPtr)
import Data.Constraint (Constraint)
import Data.Kind (Type)
import Data.SOP (All)
import Data.Hashable (Hashable)

class (Typeable t, Show t, Eq t, Serialize t, Hashable t) => Fuzzable t

instance (Typeable t, Show t, Eq t, Serialize t, Hashable t) => Fuzzable t
-- TODO: Fine grain control of Fuzzable instance
-- instance Fuzzable Int
-- instance Fuzzable Char
-- instance Fuzzable String
-- instance (Fuzzable a) => Fuzzable (VPtr a)

-- type AllFuzzable p = (All Fuzzable p, All Compos)
