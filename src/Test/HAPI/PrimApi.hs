{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

module Test.HAPI.PrimApi where

import Test.HAPI.Api ( ApiDefinition, ApiName (apiName), HasForeignDef (evalForeign), showApiFromPatDefault, HasForeign, implE )
import Test.HAPI (Attribute, args, ApiName (showApiFromPat), NP (..), Args)
import Data.Kind (Type)
import Data.SOP (K(..))
import Control.Algebra (Has)


-- | A "primitive API" that leverages pure functions in Haskell.
-- | Some transformations might be required in AASTG (e.g. y = x + 3) can be expressed using Prim API. (UB?)
-- | In addition, provides a easy-to-use interface for testing some Haskell library functions (Hooray!~)
data Prim p a = Prim { getPrimName :: String, getPrim :: Prim' p a }

data Prim' :: ApiDefinition where
  -- Normal Functions
  Arity0 :: a
         -> Prim' '[] a
  Arity1 :: (p1 -> a)
         -> Prim' '[p1] a
  Arity2 :: (p1 -> p2 -> a)
         -> Prim' '[p1, p2] a
  Arity3 :: (p1 -> p2 -> p3 -> a)
         -> Prim' '[p1, p2, p3] a
  Arity4 :: (p1 -> p2 -> p3 -> p4 -> a)
         -> Prim' '[p1, p2, p3, p4] a
  Arity5 :: (p1 -> p2 -> p3 -> p4 -> p5 -> a)
         -> Prim' '[p1, p2, p3, p4, p5] a

  -- Operators
  UnaryOp  :: (p1 -> a)
           -> Prim' '[p1] a
  BinaryOp :: (p1 -> p2 -> a)
           -> Prim' '[p1, p2] a

instance Eq (Prim p a) where
  Prim a _ == Prim b _ = a == b  -- Only compare equality via its identifier

instance ApiName Prim where
  apiName (Prim f _) = f
  {-# inline apiName #-}

  showApiFromPat (Prim f (Arity0   _)) _
    = f
  showApiFromPat (Prim f (UnaryOp  _)) (K p1 :* Nil)
    = f <> p1
  showApiFromPat (Prim f (BinaryOp _)) (K p1 :* K p2 :* Nil)
    = p1 <> " " <> f <> " " <> p2
  showApiFromPat f p
    = showApiFromPatDefault f p
  {-# inline showApiFromPat #-}


instance HasForeignDef Prim where
  evalForeign (Prim _ (Arity0 a)) _
    = return a
  evalForeign (Prim _ (Arity1 f)) [args| a |]
    = return (f a)
  evalForeign (Prim _ (Arity2 f)) [args| a b |]
    = return (f a b)
  evalForeign (Prim _ (Arity3 f)) [args| a b c |]
    = return (f a b c)
  evalForeign (Prim _ (Arity4 f)) [args| a b c d |]
    = return (f a b c d)
  evalForeign (Prim _ (Arity5 f)) [args| a b c d e |]
    = return (f a b c d e)

  evalForeign (Prim _ (UnaryOp f)) [args| a |]
    = return (f a)
  evalForeign (Prim _ (BinaryOp f)) [args| a b |]
    = return (f a b)
  {-# inline evalForeign #-}
