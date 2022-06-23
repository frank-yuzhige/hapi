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
{-# LANGUAGE DefaultSignatures #-}

module Test.HAPI.ApiTrace.CodeGen.C.DataType where
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Language.C (CExpr, CDeclSpec, CDerivedDeclr, CDeclr, CTypeSpec, CTypeSpecifier (..), undefNode, CPartDesignator (CMemberDesig), CInitializer (CInitExpr), pretty, CExtDecl, CExternalDeclaration (..))
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Data.Data (Typeable, Proxy (..))
import Test.HAPI.Constraint (type (:<>:))
import Foreign
import Foreign.C (CInt(..), CChar(..), CIntPtr(..), CLong(..), CULong(..), CUChar(..), CPtrdiff(..), CLLong(..), CULLong(..), CUInt(..), CUIntPtr(..), CSize(..), CStringLen(..), castCCharToChar, castCUCharToChar)
import Data.Hashable (Hashable)
import Data.Serialize (Serialize)
import Language.C.Data.Ident (internalIdent)
import Test.HAPI.Serialize (HSerialize)
import Data.List (intercalate)
import Data.String (fromString)
import Data.SOP (I(..))
import qualified Data.ByteString.Lazy as L
import GHC.Exts (IsList(toList))
import Data.Text.Internal.Unsafe.Char (unsafeChr)
import qualified Data.ByteString as S


data CBaseType
  = CBInt
  | CBUInt
  | CBDouble
  | CBFloat
  | CBChar
  | CBUChar
  | CBBool
  | CBUnit
  | CBNamed String
  | CBPtr   CBaseType
  | CBSum  [CBaseType]
  | CBProd [CBaseType]
  deriving (Eq, Show, Ord)

showBaseType :: CBaseType -> String
showBaseType CBInt         = "int"
showBaseType CBUInt        = "uint"
showBaseType CBDouble      = "double"
showBaseType CBFloat       = "float"
showBaseType CBChar        = "char"
showBaseType CBUChar       = "uchar"
showBaseType CBBool        = show $ pretty (CBoolType undefNode)
showBaseType CBUnit        = "unit"
showBaseType (CBNamed n)   = n
showBaseType (CBPtr t)     = "ptr_" <> showBaseType t
showBaseType (CBSum  xs)   = intercalate "__" (("S" <> show (length xs)) : map showBaseType xs)
showBaseType (CBProd xs)   = intercalate "__" (("P" <> show (length xs)) : map showBaseType xs)

baseType2CType :: CBaseType -> [CTypeSpec]
baseType2CType CBInt       = [CIntType undefNode]
baseType2CType CBUInt      = [CBoolType undefNode]
baseType2CType CBDouble    = [CDoubleType undefNode]
baseType2CType CBFloat     = [CFloatType undefNode]
baseType2CType CBChar      = [CCharType undefNode]
baseType2CType CBUChar     = [CUnsigType undefNode, CCharType undefNode]
baseType2CType CBBool      = [CBoolType undefNode]
baseType2CType CBUnit      = [CVoidType undefNode]
baseType2CType (CBNamed n) = [ty (fromString n)]
baseType2CType (CBPtr t)   = baseType2CType t
baseType2CType (CBSum xs)  = [ty (fromString $ showBaseType (CBSum  xs))]
baseType2CType (CBProd xs) = [ty (fromString $ showBaseType (CBProd xs))]

baseType2CPtrLevel :: CBaseType -> Int
baseType2CPtrLevel (CBPtr t) = baseType2CPtrLevel t + 1
baseType2CPtrLevel _         = 0

baseType2TypeDefCandidates :: CBaseType -> [CBaseType]
baseType2TypeDefCandidates t = case t of
  CBSum  xs -> t : concatMap baseType2TypeDefCandidates xs
  CBProd xs -> t : concatMap baseType2TypeDefCandidates xs
  CBPtr t   -> baseType2TypeDefCandidates  t
  _         -> []

baseType2TypeDef :: CBaseType -> CExtDecl
baseType2TypeDef t = case t of
  CBSum  xs -> CDeclExt $ union  (showBaseType t) [("s" <> show i, ts, p) | (i, m) <- [0..] `zip` xs, let (ts, p) = baseType2CGen m]
  CBProd xs -> CDeclExt $ struct (showBaseType t) [("p" <> show i, ts, p) | (i, m) <- [0..] `zip` xs, let (ts, p) = baseType2CGen m]
  _         -> error ""

baseType2CGen :: CBaseType -> ([CTypeSpec], CDeclr -> CDeclr)
baseType2CGen b = (baseType2CType b, foldr (.) id (replicate (baseType2CPtrLevel b) ptr))

toCType  :: TyConstC a => proxy a -> ([CTypeSpec], CDeclr -> CDeclr)
toCType = baseType2CGen . toCBType

ctype :: String -> (CTypeSpec, CDeclr -> CDeclr)
ctype s = (ty (internalIdent s), id)

cBytesLit :: CExpr -> CExpr -> CExpr
cBytesLit s b = cStructLit (showBaseType (CBProd [CBInt, CBPtr CBChar])) [("p0", s), ("p1", b)]

cUBytesLit :: CExpr -> CExpr -> CExpr
cUBytesLit s b = cStructLit (showBaseType (CBProd [CBInt, CBPtr CBUChar])) [("p0", s), ("p1", b)]

class Typeable a => TyConstC a where
  toCConst    :: a -> CExpr
  toCBType    :: proxy a -> CBaseType

type CCodeGen = TyConstC :<>: Typeable

instance TyConstC () where
  toCConst _ = cIntConst 0
  toCBType _ = CBUnit

instance TyConstC Int where
  toCConst   = cIntConst . fromIntegral
  toCBType _ = CBInt

instance TyConstC CInt where
  toCConst   = cIntConst . fromIntegral
  toCBType _ = CBInt

instance TyConstC CSize where
  toCConst   = cIntConst . fromIntegral
  toCBType _ = CBNamed "size_t"

instance TyConstC Bool where
  toCConst   = cBoolConst
  toCBType _ = CBBool

instance TyConstC Char where
  toCConst   = cCharConst
  toCBType _ = CBChar

instance TyConstC CChar where
  toCConst   = cIntConst . fromIntegral
  toCBType _ = CBChar

instance TyConstC Int8 where
  toCConst = cIntConst . fromIntegral
  toCBType _ = CBInt

instance TyConstC Int16 where
  toCConst = cIntConst . fromIntegral
  toCBType _ = CBInt

instance TyConstC Int32 where
  toCConst = cIntConst . fromIntegral
  toCBType _ = CBInt

instance TyConstC Int64 where
  toCConst = cIntConst . fromIntegral
  toCBType _ = CBInt

instance TyConstC String where
  toCConst s = cProdLit (showBaseType (toCBType (I s))) [toCConst (length s), cStrConst s]
  toCBType _ = CBProd [CBInt, CBPtr CBChar]

instance TyConstC L.ByteString where
  toCConst s = cProdLit (showBaseType (toCBType (I s))) [toCConst (L.length s), cStrConst (map (unsafeChr . fromIntegral) $ toList s)]
  toCBType _ = CBProd [CBInt, CBPtr CBChar]

instance TyConstC S.ByteString where
  toCConst s = cProdLit (showBaseType (toCBType (I s))) [toCConst (S.length s), cStrConst (map (unsafeChr . fromIntegral) $ toList s)]
  toCBType _ = CBProd [CBInt, CBPtr CBChar]

instance TyConstC [CChar] where
  toCConst s = cProdLit (showBaseType (toCBType (I s))) [toCConst (length s), cStrConst (map castCCharToChar s)]
  toCBType _ = CBProd [CBInt, CBPtr CBChar]

instance TyConstC [CUChar] where   --- TO typedef struct CUBytes { char * bytes; size_t size; }
  toCConst s = cProdLit (showBaseType (toCBType (I s))) [toCConst (length s), cStrConst (map castCUCharToChar s)]
  toCBType _ = CBProd [CBInt, CBPtr CBUChar]

instance TyConstC a
  => TyConstC (Ptr a) where
  toCConst   = cPtrConst
  toCBType _ = CBPtr (toCBType (Proxy @a))

instance (TyConstC a, TyConstC b)
  => TyConstC (a, b) where
  toCConst (a, b) = cProdLit (showBaseType (toCBType (I (a, b)))) [toCConst a, toCConst b]
  toCBType _      = CBProd [toCBType (Proxy @a), toCBType (Proxy @b)]

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

-- instance HSerialize Int16
