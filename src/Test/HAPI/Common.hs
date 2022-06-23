{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeApplications #-}

module Test.HAPI.Common where
import Data.Data (Typeable)
import Control.Algebra (Has, type (:+:))
import Data.Serialize (Serialize (..))
import Test.HAPI.VPtr (VPtr)
import Data.Constraint (Constraint)
import Data.Kind (Type)
import Data.SOP (All)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import GHC.Exts
import GHC.ForeignPtr (ForeignPtr(..), ForeignPtrContents(..))

class (Typeable t, Show t, Eq t, Hashable t) => Fuzzable t

instance (Typeable t, Show t, Eq t, Hashable t) => Fuzzable t

type ErrorMsg = String

deriving instance Generic (ForeignPtr a)


