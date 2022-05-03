{-# LANGUAGE DataKinds #-}
module Test.HAPI.HLib.HLibPrelude where

import qualified Prelude as P
import Test.HAPI.PrimApi (Prim(..), Prim'(..))
import Prelude (($))

-- | "Prelude" Library for the Prim Api
-- No one has time for every type hint, only where necessary :)

data HLibPreludeTag

type HLibPrelude = Prim HLibPreludeTag

(+), (-), (*) :: P.Num a => HLibPrelude '[a, a] a
(+) = Prim "+" $ BinaryOp (P.+)
(-) = Prim "-" $ BinaryOp (P.-)
(*) = Prim "*" $ BinaryOp (P.*)


(&&) = Prim "&&" $ BinaryOp (P.&&)
(||) = Prim "||" $ BinaryOp (P.||)
not  = Prim "not " $ UnaryOp P.not


len :: P.Foldable t => HLibPrelude '[t a] P.Int
len = Prim "length" $ Arity1 P.length

(==) :: P.Eq a => HLibPrelude '[a, a] P.Bool
(==) = Prim "==" $ BinaryOp (P.==)
