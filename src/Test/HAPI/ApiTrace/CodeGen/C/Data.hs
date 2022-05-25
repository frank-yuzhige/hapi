{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.HAPI.ApiTrace.CodeGen.C.Data where

import Test.HAPI.ApiTrace.Core (ApiTraceEntry(..), ApiTrace (..), trace2List)
import Language.C
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.PState ( PKey(getPKeyID, PKey), emptyPKeySet, addPKey2Set, PKeySetEntry (..), PKeySet )
import Test.HAPI.Api (ApiName (..), ApiDefinition, type (:$$:) (..))
import Data.SOP (All, NP (..))
import Test.HAPI.Constraint (type (:>>>:), castC, CMembers, productC)
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.Args (DirectAttribute (..), DirAttributes)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen, TyConstC (..))
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Data.List (nub)
import qualified Test.HAPI.Util.TypeRepMap as TM
import qualified Data.Set as S
import Data.Data (Typeable)
import Data.Type.Equality (TestEquality(..))
import Type.Reflection (typeRep)
import Data.Maybe (isJust)

class (ApiName api) => Entry2BlockC (api :: ApiDefinition) where
  entry2Block :: forall c. (CMembers CCodeGen c) => ApiTraceEntry api c -> CBlockItem
  entry2Block = entry2BlockDefault

entry2BlockDefault :: forall api c. (CMembers CCodeGen c) => ApiTraceEntry api c -> CBlockItem
entry2BlockDefault (TraceCall (x :: PKey a) api args) = case testEquality (typeRep @a) (typeRep @()) of
  Nothing    -> liftEToB $ pk2CVar x <-- (api2CVar api # dirAttrs2CExprs @c args)
  Just proof -> liftEToB $ api2CVar api # dirAttrs2CExprs @c args

entry2BlockDefault (TraceAssert p)                    = liftEToB $ cAssert (dirAttr2CExpr p)


traceDecls :: forall api c. (CMembers CCodeGen c) => [ApiTraceEntry api c] -> [CBlockItem]
traceDecls xs = concat $ TM.toListWith (\(PKeySetEntry s) -> [makeDecl k \\ mapDict (productC @CCodeGen) d | (k, d) <- S.toList s]) $ collectVar xs
  where
    collectVar :: [ApiTraceEntry api c] -> PKeySet c
    collectVar [] = emptyPKeySet
    collectVar (TraceCall (x :: PKey a) _ _ : xs)
      | isVoidTy @a = collectVar xs
      | otherwise   = addPKey2Set x \\ castC @Typeable (Dict @(c a)) $ collectVar xs
    collectVar (_                           : xs) = collectVar xs

    makeDecl :: (CCodeGen a) => PKey a -> CBlockItem
    makeDecl (x :: PKey a) = CBlockDecl $ decl (CTypeSpec ty) (f $ cDeclr $ getPKeyID x) Nothing
      where
        (ty, f) = toCType x


entryFun :: forall api c.
          ( CMembers CCodeGen c
          , Entry2BlockC api)
       => String            -- entryFunctionName
       -> ApiTrace api c    -- Trace
       -> CFunDef
entryFun fn trace = fun [intTy] fn [] body
  where
    body = CCompound [] blocks undefNode
    blocks = traceDecls (trace2List trace)
          <> map entry2Block (trace2List trace)
          <> [CBlockStmt $ creturn $ cIntConst 0]

isVoidTy :: forall a proxy. (Typeable a) => Bool
isVoidTy = isJust $ testEquality (typeRep @a) (typeRep @())

pk2CVar :: PKey a -> CExpr
pk2CVar = cVar . getPKeyID

api2CVar :: ApiName api => api p a -> CExpr
api2CVar a = cVar $ apiNameUnder "C" a

dirAttr2CExpr :: (CCodeGen a) => DirectAttribute a -> CExpr
dirAttr2CExpr (Value a) = toCConst a
dirAttr2CExpr (Get   x) = pk2CVar x

dirAttrs2CExprs :: forall c p. (All c p, CMembers CCodeGen c) => DirAttributes p -> [CExpr]
dirAttrs2CExprs Nil = []
dirAttrs2CExprs ((a :: DirectAttribute a) :* as)
  = (dirAttr2CExpr a \\ mapDict (productC @CCodeGen) (Dict @(c a))) : dirAttrs2CExprs @c as

-- instance {-# OVERLAPPABLE #-} (ApiName api) => Entry2BlockC api

instance (Entry2BlockC f, Entry2BlockC g) => Entry2BlockC (f :$$: g) where
  entry2Block :: forall c. (CMembers CCodeGen c) => ApiTraceEntry (f :$$: g) c -> CBlockItem
  entry2Block (TraceCall x (ApiL f) args) = entry2Block @f @c (TraceCall x f args)
  entry2Block (TraceCall x (ApiR g) args) = entry2Block @g @c (TraceCall x g args)
  entry2Block a                           = entry2BlockDefault a  -- TODO f or g when assert?
