{-# LANGUAGE DataKinds #-}
module Test.HAPI.PrimApi.Prelude where

import qualified Prelude as P
import Test.HAPI.PrimApi (Prim(..), Prim'(..))
import Prelude (($))

-- | "Prelude" Library for the Prim Api
-- No one has time for every type hint, only where necessary :)

(+), (-), (*) :: P.Num a => Prim '[a, a] a
(+) = Prim "+" $ BinaryOp (P.+)
(-) = Prim "-" $ BinaryOp (P.-)
(*) = Prim "*" $ BinaryOp (P.*)


(&&) = Prim "&&" $ BinaryOp (P.&&)
(||) = Prim "||" $ BinaryOp (P.||)
not  = Prim "not " $ UnaryOp P.not


len :: P.Foldable t => Prim '[t a] P.Int
len = Prim "length" $ Arity1 P.length

(==) :: P.Eq a => Prim '[a, a] P.Bool
(==) = Prim "==" $ BinaryOp (P.==)
