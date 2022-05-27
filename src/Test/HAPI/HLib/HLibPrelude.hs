{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.HAPI.HLib.HLibPrelude where

import qualified Prelude as P
import Test.HAPI.PrimApi (Prim(..), Prim'(..))
import Prelude (($))
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR))

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


-- len :: P.Foldable t => HLibPrelude '[t a] P.Int
-- len = Prim "length" $ Arity1 P.length

(==) :: P.Eq a => HLibPrelude '[a, a] P.Bool
(==) = Prim "==" $ BinaryOp (P.==)

fromIntegral :: (P.Integral a, P.Num b) => HLibPrelude '[a] b
fromIntegral = Prim "fromIntegral" $ Arity1 P.fromIntegral

fromLeft :: HLibPrelude '[P.Either a b] a
fromLeft = Prim "fromRight" $ Arity1 check
  where
    check (P.Left  a) = a
    check (P.Right _) = fatalError 'fromLeft FATAL_ERROR "Runtime error: fromLeft on a right value"

fromRight :: HLibPrelude '[P.Either a b] b
fromRight = Prim "fromRight" $ Arity1 check
  where
    check (P.Left  _) = fatalError 'fromRight FATAL_ERROR "Runtime error: fromRight on a left value"
    check (P.Right a) = a
