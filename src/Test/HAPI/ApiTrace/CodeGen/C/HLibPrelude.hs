{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Test.HAPI.ApiTrace.CodeGen.C.HLibPrelude where

import Test.HAPI.HLib.HLibPrelude (HLibPrelude)
import Test.HAPI.ApiTrace.CodeGen.C.Data (Entry2BlockC(..), entry2BlockDefault, pk2CVar, dirAttrs2CExprs)
import qualified Test.HAPI.HLib.HLibPrelude as HLib
import Test.HAPI.PrimApi (Prim(..), Prim' (BinaryOp))
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Data.SOP (NP(..))
import Test.HAPI.Constraint (CMembers, productC, dikt)
import Language.C (CBlockItem, CBinaryOp (..))
import Data.Constraint (mapDict, (\\), Dict (..))
import Test.HAPI.Args (DirectAttribute, DirAttributes)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen)
import Test.HAPI.ApiTrace.Core (ApiTraceEntry (..))

instance Entry2BlockC HLibPrelude where
  entry2Block :: forall c. (CMembers CCodeGen c) => ApiTraceEntry HLibPrelude c -> CBlockItem
  entry2Block a@TraceAssert {} = entry2BlockDefault a
  entry2Block a@(TraceCall x (Prim s ar) args) = case (s, ar) of
    ("==", BinaryOp {})
      -> liftEToB $ pk2CVar x <-- let [x, y] = dirAttrs2CExprs @c args in x ==: y
    ("+", BinaryOp {})
      -> liftEToB $ pk2CVar x <-- let [x, y] = dirAttrs2CExprs @c args in cOp CAddOp x y
    ("-", BinaryOp {})
      -> liftEToB $ pk2CVar x <-- let [x, y] = dirAttrs2CExprs @c args in cOp CSubOp x y
    ("*", BinaryOp {})
      -> liftEToB $ pk2CVar x <-- let [x, y] = dirAttrs2CExprs @c args in cOp CMulOp x y
    _    -> entry2BlockDefault a
