
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Test.HAPI.ApiTrace.CodeGen.C.HLibCString where

import Test.HAPI.ApiTrace.CodeGen.C.Util
import Test.HAPI.ApiTrace.CodeGen.C.Data (Entry2BlockC (..), call2BlockDefault, dirAttrs2CExprs, pk2CVar)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen, TyConstC (..), toCType)
import Test.HAPI.ApiTrace.Core (ApiTraceEntry (..))
import Language.C.Syntax.AST (CBlockItem, CBinaryOp (..), CExpr)
import Test.HAPI.ApiTrace.TyConst (TyConst(..))
import Data.Constraint ((\\), Dict (..), mapDict)
import Test.HAPI.PState (PKey(..))
import Test.HAPI.HLib.HLibCString (HLibCString (..))
import Data.SOP (All)
import Test.HAPI.Common (Fuzzable)
import Data.Data (Typeable)
import Test.HAPI.Args (DirAttributes)
import Data.Hashable (Hashable)
import Data.Serialize (Serialize (..))
import Test.HAPI.Serialize (HSerialize)
import Test.HAPI.Constraint (CMembers, productC)


instance Entry2BlockC HLibCString where
  call2Block :: forall c p a. (CMembers CCodeGen c, All Fuzzable p, Typeable a, All c p, c a)
             => PKey a -> HLibCString p a -> DirAttributes c p -> [CBlockItem]
  call2Block x f args = case f of
    PeekCString    -> [liftEToB $ pk2CVar x <-- let [a] = aExprs in cBytesLit (cStrlen a) a]
    PeekCStringLen -> [liftEToB $ pk2CVar x <-- let [a, b] = aExprs in cBytesLit b a]
    NewCString     -> [liftEToB $ pk2CVar x <-- let [a] = aExprs in a .: "p1"]   -- string is
    StringLen      -> [liftEToB $ pk2CVar x <-- let [a] = aExprs in cStrlen a]
    NewCBytes      -> [liftEToB $ pk2CVar x <-- let [a] = aExprs in a .: "p1"]
    CBytesLen      -> [liftEToB $ pk2CVar x <-- let [a] = aExprs in a .: "p0"]
    where
      aExprs = dirAttrs2CExprs @c args
      (ty, _) = toCType x \\ mapDict (productC @CCodeGen) (Dict @(c a))
