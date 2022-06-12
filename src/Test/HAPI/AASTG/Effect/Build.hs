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
import Test.HAPI.Args (Attribute (..), Attributes, DirectAttribute (..), var, value)
import Test.HAPI.PState (PKey(PKey))
import Test.HAPI.Effect.Eff (Algebra(alg), type (:+:) (..), Alg, send, runEnv, Eff)
import Test.HAPI.AASTG.Core (AASTG, Edge (Update, APICall, Assert, Redirect, ContIf), newAASTG, NodeID, IsValidCall)
import Test.HAPI.Api (ApiName, ApiDefinition, ApiMember (injApi))
import Test.HAPI.Common (Fuzzable)
import Control.Effect.Sum (Members, Member)
import Control.Effect.State ( State, modify, get, put )
import Control.Carrier.Fresh.Church (Fresh (Fresh), runFresh, fresh)
import Control.Algebra (Has)
import Control.Effect.Labelled (HasLabelled, sendLabelled, runLabelled, Labelled)
import Data.SOP (All, Proxy (Proxy))
import Data.Functor (($>))
import Control.Carrier.State.Church (runState)
import Control.Monad (void)
import Test.HAPI.Util.SOP (InjNP (injNP))
import Data.Data (typeRep, Typeable)
import Data.Char (toLower, isAlpha)
import Test.HAPI.AASTG.Analysis.TypeCheck (typeCheck, typeCheck', TypedAASTG)

{-
do
  x <- sNewVar (Value 10)
  y <- sNewVar Anything
  fork cont1 cont2 cont3

-}

type EdgeDir = (NodeID, NodeID)

type EdgeCon (api :: ApiDefinition) (c :: Type -> Constraint) m a = EdgeDir -> Building api c -> m a

data VAR

data Building (api :: ApiDefinition) (c :: Type -> Constraint) = Building

data BuildAASTG api c (m :: Type -> Type) a where
  NewVarB   :: Fuzzable a => proxy a -> BuildAASTG api c m (PKey a)
  NewNodeB  :: BuildAASTG api c m NodeID
  CurrNodeB :: BuildAASTG api c m NodeID
  SetNodeB  :: NodeID -> BuildAASTG api c m ()
  NewEdgeB  :: Edge api c -> BuildAASTG api c m ()

newtype BuildAASTGCA (api :: ApiDefinition) (c :: Type -> Constraint) m a = BuildAASTGCA {runBuildAASTGCA :: m a}
  deriving (Functor, Applicative, Monad)

runBuildAASTG :: forall api c sig m a any. (Alg sig m)
              => (forall sig m. Eff (BuildAASTG api c) sig m => m any)
              -> m (AASTG api c)
runBuildAASTG = runState         (\s _ -> return $ newAASTG s) []
              . runState @NodeID (\_ a -> return a) 0
              . runFresh (\_ _ -> return ()) 1
              . runLabelled @NodeID
              . runFresh (\_ _ -> return ()) 0
              . runLabelled @VAR
              . runBuildAASTGCA @api @c


runBuildTypedAASTG :: forall api c sig m a any. (Alg sig m, ApiName api)
                   => (forall sig m. Eff (BuildAASTG api c) sig m => m any)
                   -> m (TypedAASTG api c)
runBuildTypedAASTG b = do
  a <- runBuildAASTG @api @c @sig b
  return $ typeCheck' a


-- | Sender

sNewVar :: forall api c a sig m. (Has (BuildAASTG api c) sig m, Fuzzable a) => m (PKey a)
sNewVar = send (NewVarB @_ @_ @api @c (Proxy @a))

sNewNode :: forall api c sig m. Has (BuildAASTG api c) sig m => m NodeID
sNewNode = send (NewNodeB @api @c)

sCurrNode :: forall api c sig m. Has (BuildAASTG api c) sig m => m NodeID
sCurrNode = send (CurrNodeB @api @c)

sSetNode :: forall api c sig m. Has (BuildAASTG api c) sig m => NodeID -> m ()
sSetNode = send . SetNodeB @api @c

sNewEdge :: forall api c sig m. Has (BuildAASTG api c) sig m => Edge api c -> m ()
sNewEdge = send . NewEdgeB


-- | Lift to EdgeCon to make it more handy (User can write Builder <%> newNode)

newNode :: forall api c proxy sig m. Has (BuildAASTG api c) sig m => EdgeCon api c m NodeID
newNode _ _ = send (NewNodeB @api @c)

currNode :: forall api c proxy sig m. Has (BuildAASTG api c) sig m => EdgeCon api c m NodeID
currNode _ _ = send (CurrNodeB @api @c)

-- | Build Function

(%>) :: forall f. EdgeDir -> (EdgeDir -> f) -> f
d %> ma = ma d

(<%) :: forall api c proxy sig m a. (Has (BuildAASTG api c) sig m)
     => proxy api c -> (proxy api c -> m a) -> m a
p <% ma = ma p

infixr 5 %>
infixr 4 <%

(<%>) :: forall api c proxy sig m a. (Has (BuildAASTG api c) sig m)
      => Building api c -> EdgeCon api c m a -> m a
p <%> ec = do
  s <- sCurrNode @api @c
  e <- sNewNode  @api @c
  p <% (s, e) %> ec

val :: forall t api c sig m proxy. (Has (BuildAASTG api c) sig m, Fuzzable t, c t, Typeable c)
    => t -> EdgeCon api c m (PKey t)
val v = decl (value v)

decl :: forall t api c sig m proxy. (Has (BuildAASTG api c) sig m, Fuzzable t, c t, Typeable c)
     => Attribute c t -> EdgeCon api c m (PKey t)
decl attr (s, e) _ = do
  x <- sNewVar @api @c
  sNewEdge @api @c (Update s e x attr)
  sSetNode @api @c e
  return x

call_ :: forall api apis c sig m a p args proxy.
      ( Has (BuildAASTG apis c) sig m
      , ApiMember api apis
      , IsValidCall c api p
      , c a
      , Fuzzable a
      , InjNP args (Attribute c) p)
   => api p a
   -> args
   -> EdgeCon apis c m ()
call_ f args e p = void $ call @_ @apis f args e p

call :: forall api apis c sig m a p args proxy.
       ( Has (BuildAASTG apis c) sig m
       , ApiMember api apis
       , IsValidCall c api p
       , c a
       , Fuzzable a
       , InjNP args (Attribute c) p)
    => api p a
    -> args
    -> EdgeCon apis c m (PKey a)
call f args (s, e) _ = do
  x <- sNewVar @apis @c
  sNewEdge @apis @c (APICall s e x (injApi f) (injNP args))
  sSetNode @apis @c e
  return x

assert :: forall apis c sig m proxy.
       ( Has (BuildAASTG apis c) sig m
       , Fuzzable Bool
       , c Bool
       , Typeable c)
    => DirectAttribute c Bool
    -> EdgeCon apis c m ()
assert k (s, e) _ = do
  sNewEdge @apis @c (Assert s e k)
  sSetNode @apis @c e

contIf :: forall apis c sig m proxy.
        ( Has (BuildAASTG apis c) sig m
        , Fuzzable Bool
        , c Bool
        , Typeable c)
     => DirectAttribute c Bool
     -> EdgeCon apis c m ()
contIf k (s, e) _ = do
  sNewEdge @apis @c (ContIf s e k)
  sSetNode @apis @c e

redirect :: forall apis c sig m proxy.
       ( Has (BuildAASTG apis c) sig m
       , Fuzzable Bool
       , c Bool)
    => EdgeCon apis c m ()
redirect (s, e) _ = do
  sNewEdge @apis @c (Redirect s e)
  sSetNode @apis @c e

(<+>) :: forall api c sig m a b. (Has (BuildAASTG api c) sig m) => m () -> m () -> m ()
ma <+> mb = do
  s <- sCurrNode @api @c
  ma
  sSetNode @api @c s
  mb
  sSetNode @api @c s
  return ()

fork :: forall api c sig m a proxy. (Has (BuildAASTG api c) sig m) => proxy api c -> m a -> m a
fork _ f = do
  s <- sCurrNode @api @c
  a <- f
  sSetNode @api @c s
  return a

-- | Higher-level constructs

assertTrue :: forall api apis c sig m p args proxy.
            ( Has (BuildAASTG apis c) sig m
            , ApiMember api apis
            , IsValidCall c api p
            , c Bool
            , InjNP args (Attribute c) p
            , Fuzzable Bool)
          => api p Bool
          -> args
          -> EdgeCon apis c m (PKey Bool)
assertTrue f args (s, e) p = do
  i <- sNewNode @apis @c
  b <- p <%(s, i)%> call f args
  p <%(i, e)%> assert (Get b)
  return b

assertFalse :: forall api apis c sig m p args proxy.
             ( Has (BuildAASTG apis c) sig m
             , ApiMember api apis
             , IsValidCall c api p
             , c Bool
             , InjNP args (Attribute c) p
             , Fuzzable Bool)
           => api p Bool
           -> args
           -> EdgeCon apis c m (PKey Bool)
assertFalse f args (s, e) p = do
  i <- sNewNode @apis @c
  b <- p <%(s, i)%> call f args
  p <%(i, e)%> assert (DNot (Get b))
  return b

ifTrue :: forall api apis c sig m p args proxy.
            ( Has (BuildAASTG apis c) sig m
            , ApiMember api apis
            , IsValidCall c api p
            , c Bool
            , InjNP args (Attribute c) p
            , Fuzzable Bool)
          => api p Bool
          -> args
          -> EdgeCon apis c m (PKey Bool)
ifTrue f args (s, e) p = do
  i <- sNewNode @apis @c
  b <- p <%(s, i)%> call f args
  p <%(i, e)%> contIf (Get b)
  return b

ifFalse :: forall api apis c sig m p args proxy.
             ( Has (BuildAASTG apis c) sig m
             , ApiMember api apis
             , IsValidCall c api p
             , c Bool
             , InjNP args (Attribute c) p
             , Fuzzable Bool)
           => api p Bool
           -> args
           -> EdgeCon apis c m (PKey Bool)
ifFalse f args (s, e) p = do
  i <- sNewNode @apis @c
  b <- p <%(s, i)%> call f args
  p <%(i, e)%> contIf (DNot (Get b))
  return b


instance ( Has (State [Edge api c]) sig m
         , Has (State NodeID      ) sig m
         , HasLabelled VAR    Fresh sig m
         , HasLabelled NodeID Fresh sig m)
         => Algebra (BuildAASTG api c :+: sig) (BuildAASTGCA api c m) where
  alg hdl sig ctx = BuildAASTGCA $ case sig of
    L (NewVarB p) -> do
      i <- sendLabelled @VAR Fresh
      let v = PKey (mkPrefix (show (typeRep p)) : show i)
      return $ ctx $> v
      where
        mkPrefix = toLower . head . (<> "u") . filter isAlpha
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
