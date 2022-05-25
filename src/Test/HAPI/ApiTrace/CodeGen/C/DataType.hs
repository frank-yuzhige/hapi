{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.HAPI.ApiTrace.CodeGen.C.DataType where
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Language.C (CExpr, CDeclSpec, CDerivedDeclr, CDeclr, CTypeSpec, CTypeSpecifier (..), undefNode)
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Data.Data (Typeable, Proxy (..))
import Test.HAPI.Constraint (type (:<>:))
import Foreign
import Foreign.C (CInt(..), CChar(..))
import Data.Hashable (Hashable)
import Data.Serialize (Serialize)
import Language.C.Data.Ident (internalIdent)

class TyConstC a where
  toCConst :: a -> CExpr
  toCType  :: proxy a -> (CTypeSpec, CDeclr -> CDeclr)

type CCodeGen = TyConstC :<>: Typeable


instance TyConstC () where
  toCConst _ = cIntConst 0
  toCType  _ = (CIntType undefNode, id)

instance TyConstC Int where
  toCConst  = cIntConst . fromIntegral
  toCType _ = (CIntType undefNode, id)

instance TyConstC CInt where
  toCConst  = cIntConst . fromIntegral
  toCType _ = (CIntType undefNode, id)

instance TyConstC Bool where
  toCConst  = cBoolConst
  toCType _ = (CBoolType undefNode, id)

instance TyConstC Char where
  toCConst  = cCharConst
  toCType _ = (CCharType undefNode, id)

instance TyConstC CChar where
  toCConst  = cIntConst . fromIntegral
  toCType _ = (CIntType undefNode, id)

instance TyConstC String where
  toCConst  = cStrConst
  toCType _ = (CCharType undefNode, ptr)


instance TyConstC a
  => TyConstC (Ptr a) where
  toCConst  = cPtrConst
  toCType _ = (ty, ptr . f)
    where
      (ty, f) = toCType (Proxy @a)

ctype :: String -> (CTypeSpec, CDeclr -> CDeclr)
ctype s = (ty (internalIdent s), id)


-- C DataType Extra Instances
deriving instance Hashable CInt
deriving instance Serialize CInt
deriving instance Hashable CChar
deriving instance Serialize CChar
