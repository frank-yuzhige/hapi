{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Test.HAPI.ApiTrace.CodeGen.C.Util where

import           Language.C
import           Data.String
import Foreign (Ptr)
import Text.Printf (printf)

-- Internal use only

initListExprs :: [CExpr] -> CInit
initListExprs input = CInitList (fmap (\x -> ([], CInitExpr x undefNode)) input) undefNode

cVar :: String -> CExpr
cVar str = CVar (internalIdent str) undefNode

ty2Decl :: CTypeSpec -> CDecl
ty2Decl x = CDecl [CTypeSpec x] [] undefNode

cDeclr :: String -> CDeclr
cDeclr str = CDeclr (Just $ internalIdent str) [] Nothing [] undefNode

cIntConst :: Integer -> CExpr
cIntConst val = CConst (CIntConst (cInteger val) undefNode)

cBoolConst :: Bool -> CExpr
cBoolConst val = CConst (CIntConst (cInteger $ fromIntegral $ fromEnum val) undefNode)

cCharConst :: Char -> CExpr
cCharConst val = CConst (CCharConst (Language.C.cChar val) undefNode)

cStrConst :: String -> CExpr
cStrConst val = CConst (CStrConst (cString val) undefNode)

cPtrConst :: Ptr a -> CExpr
cPtrConst = undefined

defTy :: String -> CDeclSpec
defTy str = CTypeSpec $ CTypeDef (internalIdent str) undefNode

intTy :: CDeclSpec
intTy = CTypeSpec $ CIntType undefNode

floatTy :: CDeclSpec
floatTy = CTypeSpec $ CFloatType undefNode

doubleTy :: CDeclSpec
doubleTy = CTypeSpec $ CDoubleType undefNode

charTy :: CDeclSpec
charTy = CTypeSpec $ CCharType undefNode

boolTy :: CDeclSpec
boolTy = CTypeSpec $ CBoolType undefNode

voidTy :: CDeclSpec
voidTy = CTypeSpec $ CVoidType undefNode

fileTy :: CDeclSpec
fileTy = CTypeSpec $ CTypeDef (fromString "FILE") undefNode

voidSpec :: CTypeSpec
voidSpec = CVoidType undefNode

intSpec :: CTypeSpec
intSpec = CIntType undefNode

floatSpec :: CTypeSpec
floatSpec = CFloatType undefNode

idSpec :: String -> CTypeSpec
idSpec str = CTypeDef (internalIdent str) undefNode

ty :: Ident -> CTypeSpec
ty = flip CTypeDef undefNode

(#) :: CExpr -> [CExpr] -> CExpr
f # args = CCall f args undefNode

(<--) :: CExpr -> CExpr -> CExpr
var <-- val = CAssign CAssignOp var val undefNode
infixl 3 <--

liftE :: CExpr -> CStat
liftE e = CExpr (Just e) undefNode

liftEToB :: CExpr -> CBlockItem
liftEToB = CBlockStmt . liftE

cifElse :: CExpr -> CStat -> CStat -> CStat
cifElse exp th el = CIf exp th (Just el) undefNode

(&) :: CExpr -> String -> CExpr
struct & field = CMember struct (fromString field) False undefNode
infixl 8 &

data UnOp = PlusPlus
          | MinusMinus
          | Minus
          | Plus
          | Not
          | Addr -- ^ The address of operator @&@.
          | Ind -- ^ The dereferencing operator in C @*@.
          deriving(Eq, Show)

-- | Convert a 'UnOp' to the corresponding 'CUnaryOp'.
toCUnaryOp :: UnOp -> CUnaryOp
toCUnaryOp Minus = CMinOp
toCUnaryOp Plus  = CPlusOp
toCUnaryOp Not   = CNegOp
toCUnaryOp Addr  = CAdrOp
toCUnaryOp Ind   = CIndOp

cOp :: CBinaryOp -> CExpr -> CExpr -> CExpr
cOp op a b = CBinary op a b undefNode

(==:) :: CExpr -> CExpr -> CExpr
(==:) = cOp CEqOp

pre :: UnOp -> CExpr -> CExpr
PlusPlus   `pre` exp = CUnary CPreIncOp exp undefNode
MinusMinus `pre` exp = CUnary CPreDecOp exp undefNode
op         `pre` exp = CUnary (toCUnaryOp op) exp undefNode

cvoidReturn :: CStat
cvoidReturn = CReturn Nothing undefNode

creturn :: CExpr -> CStat
creturn = flip CReturn undefNode . Just

block :: [CBlockItem] -> CStat
block = flip (CCompound []) undefNode

sBlocks :: [CStat] -> CStat
sBlocks stats = CCompound [] (fmap CBlockStmt stats) undefNode

decl
  :: CDeclSpec       -- ^ The declaration specifier, usually this is a type
  -> CDeclr      -- ^ Equivalent to the name of the object being declared. Often this will
                       -- make use of the overloaded string instance for 'CDeclr's
  -> Maybe CExpr -- ^ The optional init expression
  -> CDecl
decl ty name exp = CDecl
  [ty]
  [(Just name, flip CInitExpr undefNode `fmap` exp, Nothing)]
  undefNode

decl'
  :: [CDeclSpec]       -- ^ The declaration specifier, usually this is a type
  -> CDeclr      -- ^ Equivalent to the name of the object being declared. Often this will
                       -- make use of the overloaded string instance for 'CDeclr's
  -> Maybe CExpr -- ^ The optional init expression
  -> CDecl
decl' tys name exp = CDecl
  tys
  [(Just name, flip CInitExpr undefNode `fmap` exp, Nothing)]
  undefNode

ptr :: CDeclr -> CDeclr
ptr (CDeclr nm mods cstr attrs node) =
  CDeclr nm (CPtrDeclr [] undefNode : mods) cstr attrs node

arr :: CDeclr -> CDeclr
arr (CDeclr nm mods cstr attrs node) =
  CDeclr nm (CArrDeclr [] (CNoArrSize False) undefNode : mods) cstr attrs node

justPtr :: CDeclr
justPtr = CDeclr Nothing [CPtrDeclr [] undefNode] Nothing [] undefNode

fun :: [CDeclSpec] -> String -> [Maybe CExpr -> CDecl] -> CStat -> CFunDef
fun specs name args body = annotatedFun specs name args [] body

-- | Identical to fun except this annotates the list of attributes given
-- as a list of strings.
annotatedFun
  :: [CDeclSpec]
  -> String
  -> [Maybe CExpr -> CDecl]
  -> [String]
  -> CStat
  -> CFunDef
annotatedFun specs name args annots body = CFunDef specs decl [] body undefNode
 where
  decl = CDeclr
    (Just $ fromString name)
    [CFunDeclr (Right (fmap ($ Nothing) args, False)) [] undefNode]
    Nothing
    attrs
    undefNode
  attrs :: [CAttr]
  attrs = map (\s -> CAttr (fromString s) [] undefNode) annots

funP :: [CDeclSpec] -> String -> [Maybe CExpr -> CDecl] -> CStat -> CFunDef
funP specs name args body = annotatedFunP specs name args [] body

annotatedFunP
  :: [CDeclSpec]
  -> String
  -> [Maybe CExpr -> CDecl]
  -> [String]
  -> CStat
  -> CFunDef
annotatedFunP specs name args annots body = CFunDef specs
                                                    decl
                                                    []
                                                    body
                                                    undefNode
 where
  decl = CDeclr
    (Just $ fromString name)
    [ CFunDeclr (Right (fmap ($ Nothing) args, False)) [] undefNode
    , CPtrDeclr [] undefNode
    ]
    Nothing
    attrs
    undefNode
  attrs :: [CAttr]
  attrs = map (\s -> CAttr (fromString s) [] undefNode) annots

initExp :: CExpr -> CInit
initExp exp = CInitExpr exp undefNode

initList :: CInitList -> CInit
initList xs = CInitList xs undefNode

memberDesig :: String -> CDesignator
memberDesig str = CMemberDesig (internalIdent str) undefNode

empCompoundLit :: CInitList -> CExpr
empCompoundLit xs = CCompoundLit (CDecl [] [] undefNode) xs undefNode

defCompoundLit :: String -> CInitList -> CExpr
defCompoundLit str xs =
  CCompoundLit (CDecl [defTy str] [] undefNode) xs undefNode

csu :: CStructTag -> String -> [(String, [CTypeSpec], CDeclr -> CDeclr)] -> CDecl
csu tag ident fields = CDecl
  [CStorageSpec $ CTypedef undefNode, CTypeSpec $ CSUType structTy undefNode]
  [(Just $ fromString ident, Nothing, Nothing)]
  undefNode
 where
  structTy = CStruct tag
                     (Just $ fromString ident)
                     (Just $ map structify fields)
                     []
                     undefNode
  structify (name, ty, f) = CDecl (map CTypeSpec ty)
                               [(Just (f $ fromString name), Nothing, Nothing)]
                               undefNode

csu1 :: CStructTag -> String -> [(String, [CTypeSpec], CDeclr -> CDeclr)] -> CDecl
csu1 tag ident fields = CDecl [CTypeSpec $ CSUType structTy undefNode]
                              [(Just $ fromString ident, Nothing, Nothing)]
                              undefNode
 where
  structTy = CStruct tag Nothing (Just $ map structify fields) [] undefNode
  structify (name, ty, f) =
    CDecl (map CTypeSpec ty) [(Just (f $ fromString name), Nothing, Nothing)] undefNode

csu2 :: CStructTag -> String -> [CDecl] -> CDecl
csu2 tag ident fields = CDecl
  [CStorageSpec $ CTypedef undefNode, CTypeSpec $ CSUType structTy undefNode]
  [(Just $ fromString ident, Nothing, Nothing)]
  undefNode
 where
  structTy = CStruct tag (Just $ fromString ident) (Just fields) [] undefNode

cenum :: String -> [String] -> CDecl
cenum ident fields = CDecl
  [CStorageSpec $ CTypedef undefNode, CTypeSpec $ CEnumType enumTy undefNode]
  [(Just $ fromString ident, Nothing, Nothing)]
  undefNode
 where
  enumTy = CEnum (Just $ fromString ident)
                 (Just $ map (\x -> (internalIdent x, Nothing)) fields)
                 []
                 undefNode

-- | Create a structure, for example @struct "foo" [("bar", intTy)]@ is
-- @typedef struct foo {int bar;} foo;@
struct :: String -> [(String, [CTypeSpec], CDeclr -> CDeclr)] -> CDecl
struct = csu CStructTag

-- | Equivalent to 'struct' but generates a C union instead.
union :: String -> [(String, [CTypeSpec], CDeclr -> CDeclr)] -> CDecl
union = csu CUnionTag

anoyUnion :: String -> [(String, [CTypeSpec], CDeclr -> CDeclr)] -> CDecl
anoyUnion = csu1 CUnionTag

(!) :: CExpr -> CExpr -> CExpr
arr ! ind = CIndex arr ind undefNode
infixl 8 !

(.:) :: CExpr -> String -> CExpr
struct .: tag = CMember struct (fromString tag) False undefNode
infixl 8 .:

(->:) :: CExpr -> String -> CExpr
struct ->: tag = CMember struct (fromString tag) True undefNode
infixl 8 ->:

(!:) :: String -> Int -> CExpr
varName !: ind = fromString varName ! cIntConst (fromIntegral ind)
infixl 8 !:

sizeOfDecl :: CDecl -> CExpr
sizeOfDecl decl = CSizeofType decl undefNode

sizeOfTy :: [CTypeSpec] -> CExpr
sizeOfTy ty = CSizeofType (CDecl (map CTypeSpec ty) [] undefNode) undefNode

cmalloc :: CExpr -> CExpr
cmalloc expr = fromString "malloc" # [expr]

cfree :: CExpr -> CExpr
cfree expr = fromString "free" # [expr]

cAssert :: CExpr -> CExpr
cAssert expr = fromString "assert" # [expr]

cFailure :: CExpr
cFailure = fromString "exit" # [cIntConst 1]

cStrlen :: CExpr -> CExpr
cStrlen str = fromString "strlen" # [str]

cFOpen :: CExpr -> CExpr -> CExpr
cFOpen path mode = fromString "fopen" # [path, mode]

cFClose :: CExpr -> CExpr
cFClose path = fromString "fclose" # [path]

cFPuts :: CExpr -> CExpr -> CExpr
cFPuts str stream = fromString "fputs" # [str, stream]

cAssertIf :: CExpr -> CStat
cAssertIf expr = CIf (CUnary CNegOp expr undefNode) (liftE cFailure) Nothing undefNode

cContIf :: CExpr -> CStat
cContIf expr = CIf (CUnary CNegOp expr undefNode) (creturn 0) Nothing undefNode

cNull :: CExpr
cNull = fromString "NULL"

castTo :: CExpr -> CDecl -> CExpr
exp `castTo` ty = CCast ty exp undefNode

castTy :: CExpr -> CTypeSpec -> CExpr
castTy exp ty = CCast (ty2Decl ty) exp undefNode

castTy' :: CExpr -> [CTypeSpec] -> CExpr
castTy' exp ts = CCast (CDecl (map CTypeSpec ts) [] undefNode) exp undefNode

-- | The ternary operator in C. @ternary a b c@ will turn into @a ? b : c@.
ternary :: CExpr -> CExpr -> CExpr -> CExpr
ternary i t e = CCond i (Just t) e undefNode

-- | Less-than test, @a <: b@ is equivalent to @a < b@
(<:) :: CExpr -> CExpr -> CExpr
(<:) = cOp CLeOp

-- | Greater-than test, @a >: b@ is equivalent to @a > b@
(>:) :: CExpr -> CExpr -> CExpr
(>:) = cOp CGrOp

-- | Less than or equal to, @a <=: b@ is equivalent to @a <= b@
(<=:) :: CExpr -> CExpr -> CExpr
(<=:) = cOp CLeqOp

-- | Greater than or equal to, @a >=: b@ is equivalent to @a >= b@
(>=:) :: CExpr -> CExpr -> CExpr
(>=:) = cOp CGeqOp


-- Smart constructor for CBytes

cStructLit :: String -> [(String, CExpr)] -> CExpr
cStructLit t fs = defCompoundLit t (map mkMember fs)
  where mkMember (m, e) = ([memberDesig m] , initExp e)

cUnionLit :: String -> String -> CExpr -> CExpr
cUnionLit t m e = cStructLit t [(m, e)]

cProdLit :: String -> [CExpr] -> CExpr
cProdLit t fs = cStructLit t [(fromString $ printf "p%d" i, f) | (i :: Int, f) <- [0..] `zip` fs]

cSumLit :: String -> [CExpr] -> CExpr
cSumLit t fs = cStructLit t [(fromString $ printf "s%d" i, f) | (i :: Int, f) <- [0..] `zip` fs]

instance Num CExpr where
  fromInteger = CConst . flip CIntConst undefNode . cInteger
  (*)         = cOp CMulOp
  (+)         = cOp CAddOp
  (-)         = cOp CSubOp
  abs a = ternary (a >=: 0) a (negate a)
  signum a = ternary (a >=: 0) (ternary (a ==: 0) a 1) (-1)
instance Fractional CExpr where
  (/)          = cOp CDivOp
  fromRational = CConst . flip CFloatConst undefNode . cFloat . fromRational

instance IsString Ident where
  fromString = internalIdent
instance IsString CExpr where
  fromString s = CVar (fromString s) undefNode
instance IsString CDeclr where
  fromString str = CDeclr (Just $ fromString str) [] Nothing [] undefNode
instance IsString CDecl where
  fromString str =
    CDecl [CTypeSpec (CTypeDef (fromString str) undefNode)] [] undefNode
instance IsString CTypeSpec where
  fromString = flip CTypeDef undefNode . fromString
