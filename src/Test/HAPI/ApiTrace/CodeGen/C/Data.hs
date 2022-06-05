{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE LambdaCase #-}

module Test.HAPI.ApiTrace.CodeGen.C.Data where

import Test.HAPI.ApiTrace.Core (ApiTraceEntry(..), ApiTrace (..), trace2List)
import Language.C
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.PState ( PKey(getPKeyID, PKey), emptyPKeySet, addPKey2Set, PKeySetEntry (..), PKeySet )
import Test.HAPI.Api (ApiName (..), ApiDefinition, type (:$$:) (..))
import Data.SOP (All, NP (..))
import Test.HAPI.Constraint (type (:>>>:), CMembers, productC, witnessC)
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.Args (DirectAttribute (..), DirAttributes, DACompOp (..))
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen, TyConstC (..), toCType)
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Data.List (nub)
import qualified Test.HAPI.Util.TypeRepMap as TM
import qualified Data.Set as S
import Data.Data (Typeable, Proxy (..))
import Data.Type.Equality (TestEquality(..))
import Type.Reflection (typeRep)
import Data.Maybe (isJust)
import Test.HAPI.ApiTrace.CodeGen.C.State (CCodeGenState, recordType, HasCodeGenC, recordTypes, emptyCCodeGenState)
import Control.Algebra (Has, run)
import Control.Effect.State (State)
import Control.Carrier.State.Church (runState)

class (ApiName api) => Entry2BlockC (api :: ApiDefinition) where
  call2Block :: forall c p a. (CMembers CCodeGen c, ApiName api, All Fuzzable p, Typeable a, All c p, c a)
             => PKey a -> api p a -> DirAttributes c p -> [CBlockItem]
  call2Block = call2BlockDefault

  extraDecls :: forall c p a. (CMembers CCodeGen c, ApiName api, All Fuzzable p, Typeable a, All c p, c a)
             => PKey a -> api p a -> DirAttributes c p -> [CDecl]
  extraDecls _ _ _ = []

call2BlockDefault :: forall api c p a. (CMembers CCodeGen c, ApiName api, All Fuzzable p, Typeable a, All c p, c a)
                  => PKey a -> api p a -> DirAttributes c p -> [CBlockItem]
call2BlockDefault x api args = case testEquality (typeRep @a) (typeRep @()) of
  Nothing    -> [liftEToB $ pk2CVar x <-- (api2CVar api # dirAttrs2CExprs @c args)]
  Just proof -> [liftEToB $ api2CVar api # dirAttrs2CExprs @c args]

entry2Block :: forall api c. (CMembers CCodeGen c, Entry2BlockC api) => ApiTraceEntry api c -> [CBlockItem]
entry2Block = \case
  TraceCall x api args -> call2Block x api args
  TraceAssert da       -> [CBlockStmt $ cAssertIf (dirAttr2CExpr da)]
  TraceContIf da       -> [CBlockStmt $ cContIf   (dirAttr2CExpr da)]
  TraceDirect x da     -> [liftEToB   $ pk2CVar x <-- dirAttr2CExpr da]

traceDecls :: forall api c sig m. (CMembers CCodeGen c, Entry2BlockC api, HasCodeGenC sig m) => [ApiTraceEntry api c] -> m [CBlockItem]
traceDecls xs = do
  extras <- collectExtra xs
  return $ extras <> fromVars
  where
    fromExtras = collectExtra xs
    fromVars   = concat $ TM.toListWith (\(PKeySetEntry s) -> [makeDecl k \\ mapDict (productC @CCodeGen) d | (k, d) <- S.toList s]) $ collectVar xs
    collectVar :: [ApiTraceEntry api c] -> PKeySet c
    collectVar [] = emptyPKeySet
    collectVar (TraceCall (x :: PKey a) _ _ : xs)
      | isVoidTy @a = collectVar xs
      | otherwise   = addPKey2Set x \\ witnessC @Typeable @c @a $ collectVar xs
    collectVar (TraceDirect (x :: PKey a) _ : xs)
      | isVoidTy @a = collectVar xs
      | otherwise   = addPKey2Set x \\ witnessC @Typeable @c @a $ collectVar xs
    collectVar (_                           : xs) = collectVar xs

    collectExtra :: [ApiTraceEntry api c] -> m [CBlockItem]
    collectExtra xs = concat <$> mapM go xs
      where
        go (TraceCall (x :: PKey a) f a) = do
          recordType x \\ witnessC @TyConstC @c @a
          recordTypes @c a
          return $ map CBlockDecl (extraDecls x f a)
        go (TraceDirect (x :: PKey a) a) = do
          recordType x \\ witnessC @TyConstC @c @a
          return []
        go _ = return []


    -- collectExtra []                     = []
    -- collectExtra (TraceCall x f a : xs) = map CBlockDecl (extraDecls x f a) <> collectExtra xs
    -- collectExtra (_ : xs)               = collectExtra xs

    makeDecl :: (CCodeGen a) => PKey a -> CBlockItem
    makeDecl (x :: PKey a) = CBlockDecl $ decl' (map CTypeSpec ty) (f $ cDeclr $ getPKeyID x) Nothing
      where
        (ty, f) = toCType x

entryFun :: forall api c.
          ( CMembers CCodeGen c
          , Entry2BlockC api)
       => String            -- entryFunctionName
       -> ApiTrace api c    -- Trace
       -> (CFunDef, CCodeGenState)
entryFun fn trace = (fun [intTy] fn [] body, st)
  where
    body = CCompound [] blocks' undefNode
    (st, blocks) = run $ runState (curry return) emptyCCodeGenState (traceDecls (trace2List trace))
    blocks' = blocks
          <> concatMap entry2Block (trace2List trace)
          <> [CBlockStmt $ creturn $ cIntConst 0]

traceMain :: forall api c.
           ( CMembers CCodeGen c
           , Entry2BlockC api)
        => ApiTrace api c
        ->  (CExtDecl, CCodeGenState)
traceMain trace = (CFDefExt fn, st)
  where
    (fn, st) = entryFun "main" trace

isVoidTy :: forall a proxy. (Typeable a) => Bool
isVoidTy = isJust $ testEquality (typeRep @a) (typeRep @())

pk2CVar :: PKey a -> CExpr
pk2CVar = cVar . getPKeyID

api2CVar :: ApiName api => api p a -> CExpr
api2CVar a = cVar $ apiNameUnder "C" a


dirAttrCollectType :: forall c a sig m. (CMembers CCodeGen c, c a, HasCodeGenC sig m) => DirectAttribute c a -> m ()
dirAttrCollectType _ = recordType (Proxy @a) \\ witnessC @TyConstC @c @a

dirAttrsCollectType :: forall c p sig m. (CMembers CCodeGen c, All c p, HasCodeGenC sig m) => DirAttributes c p -> m ()
dirAttrsCollectType Nil = return ()
dirAttrsCollectType (d :* ds) = dirAttrCollectType d >> dirAttrsCollectType ds

dirAttr2CExpr :: forall c a. (CMembers CCodeGen c, c a) => DirectAttribute c a -> CExpr
dirAttr2CExpr (Value a)   = toCConst a \\ mapDict (productC @CCodeGen) (Dict @(c a))
dirAttr2CExpr (Get   x)   = pk2CVar x
dirAttr2CExpr (DNot  x)   = CUnary  CNegOp (dirAttr2CExpr x) undefNode
dirAttr2CExpr (DNeg  x)   = CUnary  CMinOp (dirAttr2CExpr x) undefNode
dirAttr2CExpr (DAnd  x y) = CBinary CLndOp (dirAttr2CExpr x) (dirAttr2CExpr y) undefNode
dirAttr2CExpr (DOr   x y) = CBinary CLorOp (dirAttr2CExpr x) (dirAttr2CExpr y) undefNode
dirAttr2CExpr (DEq b x y) = CBinary op     (dirAttr2CExpr x) (dirAttr2CExpr y) undefNode
  where op = if b then CEqOp else CNeqOp
dirAttr2CExpr (DPlus  x y) = CBinary CAddOp (dirAttr2CExpr x) (dirAttr2CExpr y) undefNode
dirAttr2CExpr (DMinus x y) = CBinary CSubOp (dirAttr2CExpr x) (dirAttr2CExpr y) undefNode
dirAttr2CExpr (DMul   x y) = CBinary CMulOp (dirAttr2CExpr x) (dirAttr2CExpr y) undefNode
dirAttr2CExpr (DDiv   x y) = CBinary CDivOp (dirAttr2CExpr x) (dirAttr2CExpr y) undefNode
dirAttr2CExpr (DFDiv  x y) = CBinary CDivOp (dirAttr2CExpr x) (dirAttr2CExpr y) undefNode
dirAttr2CExpr (DCmp c x y) = CBinary op     (dirAttr2CExpr x) (dirAttr2CExpr y) undefNode
  where op = case c of
          DGt  -> CGrOp
          DGte -> CGeqOp
          DLt  -> CLeOp
          DLte -> CLeqOp
dirAttr2CExpr d@(DCastInt x :: DirectAttribute c b) = castTy' (dirAttr2CExpr x) s
  where
    (s, _) = toCType d \\ mapDict (productC @CCodeGen) (Dict @(c b))
dirAttr2CExpr DNullptr     = cNull

dirAttrs2CExprs :: forall c p. (All c p, CMembers CCodeGen c) => DirAttributes c p -> [CExpr]
dirAttrs2CExprs Nil = []
dirAttrs2CExprs ((a :: DirectAttribute c a) :* as)
  = dirAttr2CExpr a : dirAttrs2CExprs @c as

-- instance {-# OVERLAPPABLE #-} (ApiName api) => Entry2BlockC api

instance (Entry2BlockC f, Entry2BlockC g) => Entry2BlockC (f :$$: g) where
  call2Block x (ApiL f) args = call2Block x f args
  call2Block x (ApiR g) args = call2Block x g args
  extraDecls x (ApiL f) args = extraDecls x f args
  extraDecls x (ApiR g) args = extraDecls x g args
