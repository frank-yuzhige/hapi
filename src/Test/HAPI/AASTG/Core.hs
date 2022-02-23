{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.AASTG.Core where
import Test.HAPI.QVS (QVS (IntRange))
import GHC.TypeNats (Nat)
import Data.Kind (Type)
import Data.HList (HList (HCons, HNil))
import Test.HAPI.Data.NatMap (Mapping((:->)))
import qualified Test.HAPI.Data.NatMap as NM
import Test.HAPI.Lib (ArithApiA(AddA))
import Test.HAPI.Api (ApiDefinition)
import Control.Effect.Sum (Member)
import Control.Algebra (Has, Algebra)

-- Abstract API state transition graph

type PStateID = Nat

type PStateRecord = [NM.Mapping PStateID Type]

data Attribute a where
  IntR :: Int -> Int -> Attribute Int
  Get  :: NM.Var i -> Attribute a

type family ApiAttributes s (api :: Type) :: [Type] where
  ApiAttributes s (a -> r)  = (Attribute a : ApiAttributes s r)
  ApiAttributes s (api r a) = '[]

data Edge (api :: ApiDefinition) where
  APICall :: (Member a api) => Int -> Int -> a m x -> HList (ApiAttributes s (a m x)) -> Edge api

start :: Edge api -> Int
start (APICall s _ _ _) = s

end :: Edge api -> Int
end (APICall _ e _ _) = e

data AASTG api = AASTG {
  getStart :: Int,
  getEdges :: [Edge api]
}

edgesFrom :: Int -> AASTG api -> [Edge api]
edgesFrom i (AASTG _ es) = filter ((== i) . start) es

edgesTo :: Int -> AASTG api -> [Edge api]
edgesTo i (AASTG _ es) = filter ((== i) . end) es

synthStub :: forall api sig m. (Has api sig m) => AASTG api -> [m ()]
synthStub aastg@(AASTG start edges) = synth start
  where
    synth i = return ()
            : concat [(synthOneStep e >>) <$> synth (end e) | e <- edgesFrom i aastg]
    synthOneStep (APICall s e api args) = do
      -- TODO
      -- 1. Resolve Attributes (Into QVS)
      -- 2. Make APICall using attributes
      -- 3. Check if return value satisfies
      -- 4. Store return value in state
      return ()
