{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.HAPI.Common where
import Data.Data (Typeable)
import Control.Algebra (Has, type (:+:))
import Data.Serialize (Serialize)

class (Typeable t, Show t, Serialize t) => Fuzzable t

instance (Typeable t, Show t, Serialize t) => Fuzzable t
