{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Test.HAPI.ApiTrace.CodeGen.C.HLibPtr where

import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.ApiTrace.CodeGen.C.Data (Entry2BlockC (..), entry2BlockDefault, dirAttrs2CExprs, pk2CVar)
import Test.HAPI.HLib.HLibPtr (HLibPtr (..))
import Test.HAPI.Constraint (CMembers, castC, productC)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen, TyConstC (..))
import Test.HAPI.ApiTrace.Core (ApiTraceEntry (..))
import Language.C.Syntax.AST (CBlockItem, CBinaryOp (..), CExpr, CDeclarationSpecifier (CTypeSpec))
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.PState (PKey(..))


instance Entry2BlockC HLibPtr where
  entry2Block :: forall c. (CMembers CCodeGen c) => ApiTraceEntry HLibPtr c -> [CBlockItem]
  entry2Block a@TraceAssert {} = entry2BlockDefault a
  entry2Block a@(TraceCall (x :: PKey a) f args) = case f of
    CastPtr     -> [liftEToB $ pk2CVar x <-- let [a]       = aExprs in castTo a (decl ty' justPtr Nothing)]
    PlusPtr     -> [liftEToB $ pk2CVar x <-- let [a, b]    = aExprs in cOp CAddOp a b]
    MinusPtr    -> [liftEToB $ pk2CVar x <-- let [a, b]    = aExprs in cOp CSubOp a b]
    PeekPtr     -> [liftEToB $ pk2CVar x <-- let [a]       = aExprs in Ind `pre` a]
    PokePtr     -> [liftEToB $               let [a, b]    = aExprs in Ind `pre` a <-- b]
    Malloc      -> [liftEToB $ pk2CVar x <-- cmalloc (sizeOfTy ty)]
    MallocBytes -> [liftEToB $ pk2CVar x <-- let [a]       = aExprs in cmalloc a]
    Free        -> [liftEToB $ pk2CVar x <-- let [a]       = aExprs in cfree a]
    where
      aExprs = dirAttrs2CExprs @c args
      (ty, _) = toCType x \\ mapDict (productC @CCodeGen) (Dict @(c a))
      ty' = CTypeSpec ty
