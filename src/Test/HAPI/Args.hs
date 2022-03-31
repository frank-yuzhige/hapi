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
{-# LANGUAGE ScopedTypeVariables #-}

module Test.HAPI.Args where
import Data.HList (HList (HCons, HNil), HBuild', HList2List (hList2List))
import GHC.Base (Nat)
import Data.Kind (Type)
import GHC.TypeLits (type (-), type (+))
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Quote (QuasiQuoter (quoteDec, quotePat, quoteType, quoteExp, QuasiQuoter))
import Data.Data (Proxy)
import Data.HList.HList (hBuild)
import Data.HList.CommonMain (hEnd)
import Data.SOP (NP (Nil, (:*)), All)
import Data.Functor.Identity (Identity (Identity))
import Data.List (intercalate)
import Language.Haskell.Meta (parseExp)

type Args a = NP Identity a

pattern (::*) :: x -> Args xs -> Args (x : xs)
pattern a ::* b = Identity a :* b
{-# COMPLETE (::*) :: NP #-}
infixr 2 ::*

noArgs :: Args '[]
noArgs = Nil

showArgs :: forall p. All Show p => Args p -> String
showArgs args = "(" <> intercalate ", " (go args) <> ")"
  where
    go :: forall p. All Show p => Args p -> [String]
    go Nil                = []
    go (Identity a :* as) = show a : go as

args :: QuasiQuoter
args = QuasiQuoter {
    quoteExp = exp . words,
    quoteType = err,
    quotePat = pat . words,
    quoteDec = err
  }
  where
    err = error "args is for pattern"
    pat []       = [p|Nil|]
    pat (x : xs) = [p|Identity $(return (if x == "_" then WildP else VarP (mkName x))) :* $(pat xs)|]
    exp []       = [e|Nil|]
    exp (x : xs) = case parseExp x of
      Left err -> fail err
      Right r  -> [e|Identity $(return r) :* $(exp xs)|]
