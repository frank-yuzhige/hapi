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
-- TODO: Fine grain control of Fuzzable instance
-- instance Fuzzable Int
-- instance Fuzzable Char
-- instance Fuzzable String
-- instance (Fuzzable a) => Fuzzable (VPtr a)

-- type AllFuzzable p = (All Fuzzable p, All Compos)

deriving instance Generic (ForeignPtr a)


-- instance Serialize ForeignPtrContents where
--   put (PlainForeignPtr ir) = _wa
--   put (MallocPtr mba ir) = _wb
--   put (PlainPtr mba) = _wc

-- instance Serialize (ForeignPtr a) where
--   -- put p = put (castPtr2Int p)
--   -- get   = castInt2Ptr <$> get @Int


