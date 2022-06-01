{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Test.HAPI.ApiTrace.CodeGen.C.HLibPrelude where

import Test.HAPI.HLib.HLibPrelude (HLibPrelude)
import Test.HAPI.ApiTrace.CodeGen.C.Data (Entry2BlockC(..),  pk2CVar, dirAttrs2CExprs, call2BlockDefault)
import qualified Test.HAPI.HLib.HLibPrelude as HLib
import Test.HAPI.PrimApi (Prim(..), Prim' (BinaryOp))
import Test.HAPI.ApiTrace.CodeGen.C.Util
import Data.SOP (NP(..))
import Test.HAPI.Constraint (CMembers, productC)
import Language.C (CBlockItem, CBinaryOp (..))
import Data.Constraint (mapDict, (\\), Dict (..))
import Test.HAPI.Args (DirectAttribute, DirAttributes)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen)
import Test.HAPI.ApiTrace.Core (ApiTraceEntry (..))

instance Entry2BlockC HLibPrelude where
  call2Block x a@(Prim s ar) (args :: DirAttributes c p) = case (s, ar) of
    ("==", BinaryOp {})
      -> [liftEToB $ pk2CVar x <-- let [x, y] = dirAttrs2CExprs @c args in x ==: y]
    ("+", BinaryOp {})
      -> [liftEToB $ pk2CVar x <-- let [x, y] = dirAttrs2CExprs @c args in cOp CAddOp x y]
    ("-", BinaryOp {})
      -> [liftEToB $ pk2CVar x <-- let [x, y] = dirAttrs2CExprs @c args in cOp CSubOp x y]
    ("*", BinaryOp {})
      -> [liftEToB $ pk2CVar x <-- let [x, y] = dirAttrs2CExprs @c args in cOp CMulOp x y]
    -- TODO
    _    -> call2BlockDefault x a args
