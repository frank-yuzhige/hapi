{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.AASTG.Analysis.TypeCheck where

import Test.HAPI.AASTG.Core (AASTG (AASTG), NodeID, Edge (..), edgesFrom, endNode, allNodes)
import Test.HAPI.PState (PKey(getPKeyID, PKey))
import Test.HAPI.Args (Attributes, Attribute (..), DirectAttribute (Get))
import Test.HAPI.Common (Fuzzable)
import Test.HAPI.Effect.Eff (Eff, type (:+:), Alg, debug, runEnv)

import Data.Map (Map)
import Data.Data
  ( TypeRep, typeOf, Typeable, typeRep, Proxy(Proxy), Proxy )
import Data.TypeRepMap (TypeRepMap)
import Control.Effect.State ( State, modify, gets )
import Control.Carrier.State.Church (runState)
import Control.Carrier.Error.Church (runError, throwError)
import Control.Effect.Error (Error)
import Control.Lens ( makeLenses, view, over )
import Data.SOP (hcmap, NP (Nil, (:*)), All)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Set (Set)
import Data.IntMap (IntMap)
import Control.Monad (unless, forM_)
import Data.String (IsString(fromString))

import qualified Data.Map.Strict as M
import qualified Data.TypeRepMap as TM
import qualified Data.IntMap     as IM
import qualified Data.Set        as S
import Test.HAPI.AASTG.Analysis.ProcType (inferProcType, inferProcTypeUB, UnboundedProcTypeMap, ProcType, (!*))
import Test.HAPI.AASTG.Analysis.ProcCtx (ProcCtxMap, ProcCtx, deriveProcCtxs, memberCtx, deriveProcCtxsUB)
import Test.HAPI.Api (ApiName)
import Text.Printf (printf)
import Data.Either (fromRight)
import Test.HAPI.Util.TH (fatalError, FatalErrorKind (FATAL_ERROR))
import Control.Applicative ((<|>))

type EdgeRep = String
type PKeyRep = String

data TypeCheckCtx = TypeCheckCtx { procTypes :: UnboundedProcTypeMap, procCtxs :: ProcCtxMap } deriving Show

data TypeCheckError = TypeCheckError NodeID EdgeRep TypeErrorCause
  deriving (Show)

data TypedAASTG api c = TypedAASTG
  { typeCheckCtx :: TypeCheckCtx
  , castAASTG    :: AASTG api c
  }
  deriving (Show)

data TypeErrorCause
  = UseVariableNotInContext String ProcCtx
  -- | ReassignVariable        String ProcCtx
  deriving (Show)

typeCheck' :: ApiName api => AASTG api c -> TypedAASTG api c
typeCheck' a = fromRight (fatalError 'typeCheck' FATAL_ERROR "123123123") $ runEnv $ typeCheckEither a

typeCheckEither :: forall api c sig m.
                 ( Alg sig m
                 , ApiName api)
              => AASTG api c
              -> m (Either TypeCheckError (TypedAASTG api c))
typeCheckEither = runError (return . Left) (return . Right) . typeCheck
{-# INLINE typeCheckEither #-}

typeCheck :: forall api c sig m.
           ( Eff (Error TypeCheckError) sig m
           , ApiName api)
        => AASTG api c
        -> m (TypedAASTG api c)
typeCheck aastg = do
  pts  <- inferProcTypeUB aastg
  -- debug $ printf "%s: pts = %s" (show 'typeCheck) (show pts)
  ctxs <- deriveProcCtxsUB pts
  forM_ (allNodes aastg) (check ctxs)
  return $ TypedAASTG (TypeCheckCtx pts ctxs) aastg
  where
    check ctxs i = do
      forM_ (edgesFrom i aastg) $ \edge -> do
        s <- checkEdge (ctxs IM.! i) edge
        case s of
          Nothing  -> return ()
          Just err -> throwError $ TypeCheckError i (show edge) err

      -- forM_ (edgesFrom i aastg) $ \edge -> case edge of
      --   Update   _ _ k a      -> checkAttr edge a
      --   ContIf   _ _ p        -> checkAttr edge (Direct p)
      --   Assert   _ _ p        -> checkAttr edge (Direct p)
      --   APICall  _ _ k f args -> checkArgs edge args
      --   Redirect _ _          -> return ()
      -- where
      --   ctx = ctxs IM.! i

      --   checkArgs :: forall p. Edge api c -> Attributes p -> m ()
      --   checkArgs edge Nil       = return ()
      --   checkArgs edge (a :* as) = checkAttr edge a >> checkArgs edge as

      --   checkAttr :: forall a. Edge api c -> Attribute a -> m ()
      --   checkAttr edge = \case
      --     Direct (Get x) ->
      --       if x `memberCtx` ctx
      --         then return ()
      --         else throwError $ TypeCheckError i (show edge) $ UseVariableNotInContext (getPKeyID x) ctx
      --     AnyOf as -> mapM_ (checkAttr edge) as
      --     _        -> return ()

checkEdge :: forall api c sig m.
           (ApiName api
           , Alg sig m)
        => ProcCtx
        -> Edge api c
        -> m (Maybe TypeErrorCause)
checkEdge ctx edge = case edge of
  Update   _ _ k a      -> checkAttr a
  ContIf   _ _ p        -> checkAttr (Direct p)
  Assert   _ _ p        -> checkAttr (Direct p)
  APICall  _ _ k f args -> checkArgs args
  Redirect _ _          -> return Nothing
  where
    checkArgs :: forall p. Attributes c p -> m (Maybe TypeErrorCause)
    checkArgs Nil       = return Nothing
    checkArgs (a :* as) = do
      x <- checkAttr a
      y <- checkArgs as
      return (x <|> y)

    checkAttr :: forall a. Attribute c a -> m (Maybe TypeErrorCause)
    checkAttr = \case
      Direct (Get x) ->
        if x `memberCtx` ctx
          then return Nothing
          else return $ Just $ UseVariableNotInContext (getPKeyID x) ctx
      -- AnyOf as -> foldr (<|>) Nothing <$> mapM checkAttr as
      _        -> return Nothing


procTypeUBOf :: NodeID -> TypedAASTG api c -> ProcType
procTypeUBOf i (TypedAASTG (TypeCheckCtx uptm pcm) _) = uptm !* i

procCtxOf :: NodeID -> TypedAASTG api c -> ProcCtx
procCtxOf i (TypedAASTG (TypeCheckCtx uptm pcm) _) = pcm IM.! i
