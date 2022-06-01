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
{-# LANGUAGE OverloadedStrings #-}

module Test.HAPI.ApiTrace.CodeGen.C.DataType where
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Language.C (CExpr, CDeclSpec, CDerivedDeclr, CDeclr, CTypeSpec, CTypeSpecifier (..), undefNode, CPartDesignator (CMemberDesig), CInitializer (CInitExpr))
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Data.Data (Typeable, Proxy (..))
import Test.HAPI.Constraint (type (:<>:))
import Foreign
import Foreign.C (CInt(..), CChar(..), CIntPtr(..), CLong(..), CULong(..), CUChar(..), CPtrdiff(..), CLLong(..), CULLong(..), CUInt(..), CUIntPtr(..), CSize(..), CStringLen(..), castCCharToChar, castCUCharToChar)
import Data.Hashable (Hashable)
import Data.Serialize (Serialize)
import Language.C.Data.Ident (internalIdent)
import Test.HAPI.Serialize (HSerialize)

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

instance TyConstC CSize where
  toCConst  = cIntConst . fromIntegral
  toCType _ = (ty (internalIdent "size_t"), id)

instance TyConstC Bool where
  toCConst  = cBoolConst
  toCType _ = (CBoolType undefNode, id)

instance TyConstC Char where
  toCConst  = cCharConst
  toCType _ = (CCharType undefNode, id)

instance TyConstC CChar where
  toCConst  = cIntConst . fromIntegral
  toCType _ = (CCharType undefNode, id)

instance TyConstC String where   --- TO typedef struct CBytes { char * bytes; size_t size; }
  toCConst s = cBytesLit (cStrConst s) (toCConst (length s))
  toCType _  = ctype "CBytes"

instance TyConstC [CChar] where   --- TO typedef struct CBytes { char * bytes; size_t size; }
  toCConst s = cBytesLit (cStrConst (map castCCharToChar s)) (toCConst (length s))
  toCType _  = ctype "CBytes"

instance TyConstC [CUChar] where   --- TO typedef struct CBytes { char * bytes; size_t size; }
  toCConst s = cBytesLit (cStrConst (map castCUCharToChar s)) (toCConst (length s))
  toCType _  = ctype "CBytes"

instance TyConstC a
  => TyConstC (Ptr a) where
  toCConst  = cPtrConst
  toCType _ = (t, ptr . f)
    where
      (t, f) = toCType (Proxy @a)

ctype :: String -> (CTypeSpec, CDeclr -> CDeclr)
ctype s = (ty (internalIdent s), id)

-- C DataType Extra Instances
deriving instance Hashable CInt
deriving instance Serialize CInt
instance HSerialize CInt

deriving instance Hashable CUInt
deriving instance Serialize CUInt
instance HSerialize CUInt

deriving instance Hashable CChar
deriving instance Serialize CChar
instance HSerialize CChar

deriving instance Hashable CLong
deriving instance Serialize CLong
instance HSerialize CLong

deriving instance Hashable CLLong
deriving instance Serialize CLLong
instance HSerialize CLLong

deriving instance Hashable CULong
deriving instance Serialize CULong
instance HSerialize CULong

deriving instance Hashable CULLong
deriving instance Serialize CULLong
instance HSerialize CULLong

deriving instance Hashable CUChar
deriving instance Serialize CUChar
instance HSerialize CUChar

deriving instance Hashable CSize
deriving instance Serialize CSize
instance HSerialize CSize

deriving instance Hashable CIntPtr
deriving instance Serialize CIntPtr
instance HSerialize CIntPtr

deriving instance Hashable CUIntPtr
deriving instance Serialize CUIntPtr
instance HSerialize CUIntPtr

deriving instance Hashable CPtrdiff
deriving instance Serialize CPtrdiff
instance HSerialize CPtrdiff
