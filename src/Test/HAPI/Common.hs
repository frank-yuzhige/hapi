{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}

module Test.HAPI.Common where
import Data.Data (Typeable)
import Control.Algebra (Has, type (:+:))
import Test.HAPI.Property (PropertyA)

type Fuzzable t = (Typeable t, Show t)
