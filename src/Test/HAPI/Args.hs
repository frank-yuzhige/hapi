{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.Args where
import Data.HList (HList (HCons, HNil), HBuild')
import GHC.Base (Nat)
import Data.Kind (Type)
import GHC.TypeLits (type (-), type (+))
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Quote (QuasiQuoter (quoteDec, quotePat, quoteType, quoteExp, QuasiQuoter))
import Data.Data (Proxy)
import Data.HList.HList (hBuild)
import Data.HList.CommonMain (hEnd)
import Data.SOP (NP (Nil, (:*)))
import Data.Functor.Identity (Identity (Identity))

type Args a = HList a

pattern (:::) :: x -> Args xs -> Args (x : xs)
pattern a ::: b = HCons a b
{-# COMPLETE (:::) :: HList #-}
infixr 2 :::

noArgs :: Args '[]
noArgs = HNil

mkArgs :: (HBuild' '[] r) => r
mkArgs = hBuild

np2Args :: (forall t. f t -> t) -> NP f a -> Args a
np2Args _   Nil        = HNil
np2Args alg (fa :* np) = alg fa ::: np2Args alg np

args :: QuasiQuoter
args = QuasiQuoter {
    quoteExp = err,
    quoteType = err,
    quotePat = pat . words,
    quoteDec = err
  }
  where
    err = error "args is for pattern"
    pat []       = [p|HNil|]
    pat (x : xs) = [p|(HCons $(return (if x == "_" then WildP else VarP (mkName x))) $(pat xs))|]

