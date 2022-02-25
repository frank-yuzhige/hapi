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

type Args a = HList a

pattern (:::) :: x -> Args xs -> Args (x : xs)
pattern a ::: b = HCons a b
{-# COMPLETE (:::) :: HList #-}
infixr 2 :::

noArgs :: Args '[]
noArgs = HNil

mkArgs :: (HBuild' '[] r) => r
mkArgs = hBuild

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

