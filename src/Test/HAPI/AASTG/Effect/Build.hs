{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.AASTG.Effect.Build where
import Data.Kind (Type, Constraint)
import Test.HAPI.Args (Attribute (..), Attributes, DirectAttribute (Value))
import Test.HAPI.PState (PKey(PKey))
import Test.HAPI.Effect.Eff (Algebra(alg), type (:+:) (..), Alg, send, runEnv, Eff)
import Test.HAPI.AASTG.Core (AASTG, Edge (Update, APICall), newAASTG, NodeID, IsValidCall)
import Test.HAPI.Api (ApiName, ApiDefinition, ApiMember (injApi), newVPtr)
import Test.HAPI.Common (Fuzzable)
import Control.Effect.Sum (Members, Member)
import Control.Effect.State ( State, modify, get, put )
import Control.Carrier.Fresh.Church (Fresh (Fresh), runFresh, fresh)
import Control.Algebra (Has)
import Control.Effect.Labelled (HasLabelled, sendLabelled, runLabelled, Labelled)
import Data.SOP (All)
import Data.Functor (($>))
import Control.Carrier.State.Church (runState)
import Control.Monad (void)
import Test.HAPI.Util.SOP (InjNP (injNP))

{-
do
  x <- newVar (Value 10)
  y <- newVar Anything
  fork cont1 cont2 cont3

-}

type EdgeDir = (NodeID, NodeID)

type EdgeCon proxy (api :: ApiDefinition) (c :: Type -> Constraint) m a = EdgeDir -> proxy api c -> m a

data VAR

data Building (api :: ApiDefinition) (c :: Type -> Constraint) = Building

data BuildAASTG api c (m :: Type -> Type) a where
  NewVarB   :: BuildAASTG api c m (PKey a)
  NewNodeB  :: BuildAASTG api c m NodeID
  CurrNodeB :: BuildAASTG api c m NodeID
  SetNodeB  :: NodeID -> BuildAASTG api c m ()
  NewEdgeB  :: Edge api c -> BuildAASTG api c m ()

newtype BuildAASTGCA (api :: ApiDefinition) (c :: Type -> Constraint) m a = BuildAASTGCA {runBuildAASTGCA :: m a}
  deriving (Functor, Applicative, Monad)

runBuildAASTG :: forall api c sig m a. (Alg sig m)
              => (forall sig m. Eff (BuildAASTG api c) sig m => m ())
              -> m (AASTG api c)
runBuildAASTG = runState         (\s _ -> return $ newAASTG s) []
              . runState @NodeID (\_ a -> return a) 0
              . runFresh (\_ _ -> return ()) 1
              . runLabelled @NodeID
              . runFresh (\_ _ -> return ()) 0
              . runLabelled @VAR
              . runBuildAASTGCA @api @c
-- | Sender

newVar :: forall api c a sig m. Has (BuildAASTG api c) sig m => m (PKey a)
newVar = send (NewVarB @api @c)

newNode :: forall api c sig m. Has (BuildAASTG api c) sig m => m NodeID
newNode = send (NewNodeB @api @c)

currNode :: forall api c sig m. Has (BuildAASTG api c) sig m => m NodeID
currNode = send (CurrNodeB @api @c)

setNode :: forall api c sig m. Has (BuildAASTG api c) sig m => NodeID -> m ()
setNode = send . SetNodeB @api @c

newEdge :: forall api c sig m. Has (BuildAASTG api c) sig m => Edge api c -> m ()
newEdge = send . NewEdgeB

-- | Build Function

(%>) :: forall f. EdgeDir -> (EdgeDir -> f) -> f
d %> ma = ma d

(<%) :: forall api c proxy sig m a. (Has (BuildAASTG api c) sig m)
     => proxy api c -> (proxy api c -> m a) -> m a
p <% ma = ma p

infixr 5 %>
infixr 4 <%

(<%>) :: forall api c proxy sig m a. (Has (BuildAASTG api c) sig m)
      => proxy api c -> EdgeCon proxy api c m a -> m a
p <%> ec = do
  s <- currNode @api @c
  e <- newNode  @api @c
  p <% (s, e) %> ec

val :: forall t api c sig m proxy. (Has (BuildAASTG api c) sig m, Fuzzable t, c t)
    => t -> EdgeCon proxy api c m (PKey t)
val v = var (Direct $ Value v)

var :: forall t api c sig m proxy. (Has (BuildAASTG api c) sig m, Fuzzable t, c t)
    => Attribute t -> EdgeCon proxy api c m (PKey t)
var attr (s, e) _ = do
  x <- newVar @api @c
  newEdge @api @c (Update s e x attr)
  setNode @api @c e
  return x

call :: forall api apis c sig m a p t proxy.
      ( Has (BuildAASTG apis c) sig m
      , ApiMember api apis
      , IsValidCall c api p
      , InjNP t Attribute p
      , Fuzzable a)
   => api p a
   -> t
   -> EdgeCon proxy apis c m ()
call f args e p = void $ vcall @_ @apis f args e p
  -- s <- currNode @apis @c
  -- e <- newNode @apis @c
  -- newEdge @apis @c (APICall s e Nothing (injApi f) args)
  -- setNode @apis @c e

vcall :: forall api apis c sig m a p t proxy.
       ( Has (BuildAASTG apis c) sig m
       , ApiMember api apis
       , IsValidCall c api p
       , InjNP t Attribute p
       , Fuzzable a)
    => api p a
    -> t
    -> EdgeCon proxy apis c m (PKey a)
vcall f args (s, e) _ = do
  x <- newVar @apis @c
  newEdge @apis @c (APICall s e x (injApi f) (injNP args))
  setNode @apis @c e
  return x

(<+>) :: forall api c sig m a b. (Has (BuildAASTG api c) sig m) => m () -> m () -> m ()
ma <+> mb = do
  s <- currNode @api @c
  ma
  setNode @api @c s
  mb
  setNode @api @c s
  return ()

fork :: forall api c sig m a proxy. (Has (BuildAASTG api c) sig m) => proxy api c -> m a -> m a
fork _ f = do
  s <- currNode @api @c
  a <- f
  setNode @api @c s
  return a

instance ( Has (State [Edge api c]) sig m
         , Has (State NodeID      ) sig m
         , HasLabelled VAR    Fresh sig m
         , HasLabelled NodeID Fresh sig m)
         => Algebra (BuildAASTG api c :+: sig) (BuildAASTGCA api c m) where
  alg hdl sig ctx = BuildAASTGCA $ case sig of
    L NewVarB -> do
      i <- sendLabelled @VAR Fresh
      let v = PKey $ "v" <> show i
      return $ ctx $> v
    L NewNodeB -> do
      n <- sendLabelled @NodeID Fresh
      return $ ctx $> n
    L CurrNodeB -> do
      n <- get @NodeID
      return $ ctx $> n
    L (SetNodeB n) -> do
      put n
      return $ ctx $> ()
    L (NewEdgeB e) -> do
      modify (e :)
      return $ ctx $> ()
    R other   -> alg (runBuildAASTGCA . hdl) other ctx
