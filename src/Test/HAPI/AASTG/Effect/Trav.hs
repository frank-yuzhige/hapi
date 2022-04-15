{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.AASTG.Effect.Trav where
import Data.Kind (Type, Constraint)
import Test.HAPI.AASTG.Core (Edge, NodeID, AASTG (getStart), startNode, endNode, edgesFrom)
import Control.Algebra (Algebra (alg), type (:+:) (R, L), Has, send)
import Test.HAPI.Api (ApiDefinition)
import Control.Monad (join, forM_)
import Data.Functor (($>))
import Test.HAPI.AASTG.Analysis.Path (outPaths, pathAsList, Path)
import Data.Foldable (sequenceA_, traverse_)
import qualified Data.Vector as V

data Trav api c (m :: Type -> Type) a where
  OnEvent :: TravEvent api c -> Trav api c m ()

data TravEvent api c = OnEdge (Edge api c) | OnNode NodeID

newtype TravHandler api c m = TravHandler { runTravHandler :: TravEvent api c -> m () }

newtype TravCA api c m a = TravCA { runTravCA :: TravHandler api c m -> m a }

onEvent :: Has (Trav api c) sig m => TravEvent api c -> m ()
onEvent = send . OnEvent

runTrav :: TravHandler api c m -> TravCA api c m a -> m a
runTrav = flip runTravCA

-- | Traverse Strategy

travDFS :: forall api c sig m. Has (Trav api c) sig m
        => AASTG api c -> m ()
travDFS aastg = trav (getStart aastg) -- traverse_ travPath $ outPaths (getStart aastg) aastg
  where
    trav :: NodeID -> m ()
    trav i = do
      onEvent @api @c $ OnNode i
      forM_ (edgesFrom i aastg) $ \edge -> do
        onEvent @api @c $ OnEdge edge
        trav (endNode edge)

travPath :: forall p api c sig m. (Has (Trav api c) sig m, Path p)
         => p api c -> m ()
travPath p = sequenceA_ [onEvent e | e <- events (pathAsList p)]
  where
    events []       = error "This is impossible"
    events [e]      = [OnNode (startNode e), OnEdge e, OnNode (endNode e)]
    events (e : es) = [OnNode (startNode e), OnEdge e] <> events es

instance Functor m => Functor (TravCA api c m) where
  fmap f (TravCA g) = TravCA $ fmap f . g

instance Applicative m => Applicative (TravCA api c m) where
  pure a                = TravCA $ \_ -> pure a
  TravCA f <*> TravCA g = TravCA $ \h -> f h <*> g h

instance Monad m => Monad (TravCA api c m) where
  mn >>= f = TravCA $ \h -> (`runTravCA` h) . f =<< runTravCA mn h


instance (Algebra sig m) => Algebra (Trav api c :+: sig) (TravCA api c m) where
  alg hdl sig ctx = TravCA $ \th -> case sig of
    L (OnEvent e) -> do
      runTravHandler th e
      return (ctx $> ())
    R other       -> alg ((`runTravCA` th) . hdl) other ctx
