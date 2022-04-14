{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Test.HAPI.AASTG.Analysis.TypeCheck (
  typeCheck
) where

import Test.HAPI.AASTG.Core (AASTG (AASTG), NodeID, Edge (Update, APICall, Assert, Forget), edgesFrom, endNode)
import Test.HAPI.PState (PKey(getPKeyID, PKey))
import Test.HAPI.Args (Attributes, Attribute (AnyOf, Get))
import Test.HAPI.Common (Fuzzable)

import Data.Map (Map)
import Data.Data
  ( TypeRep, typeOf, Typeable, typeRep, Proxy(Proxy), Proxy )
import Data.TypeRepMap (TypeRepMap)
import Control.Effect.State ( State, modify, gets )
import Control.Carrier.State.Church (runState)
import Control.Carrier.Error.Church (runError, throwError)
import Control.Effect.Error (Error)
import Control.Algebra (run, Has, type (:+:))
import Control.Lens ( makeLenses, view, over )
import Data.SOP (hcmap, NP (Nil, (:*)), All)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Set (Set)
import Control.Monad (unless, forM_)
import Data.String (IsString(fromString))

import qualified Data.Map.Strict as M
import qualified Data.TypeRepMap as TM
import qualified Data.Set        as S

type StateType = Map String TypeRep
type EdgeRep = Text

data Ctx = Ctx { _states :: Map NodeID StateType, _checkedNodes :: Set NodeID } deriving Show

$(makeLenses ''Ctx)

data TypeCheckError = TypeCheckError NodeID EdgeRep

typeCheck :: forall api c. AASTG api c -> Maybe TypeCheckError
typeCheck aastg@(AASTG start fs ts) = run
  . runError (return . Just) (const $ return Nothing)
  . runState (\s a -> return ()) (Ctx M.empty S.empty)
  $ checking start
  where
    checking :: forall sig m. (Has (State Ctx :+: Error TypeCheckError) sig m) => NodeID -> m ()
    checking i = do
      checked <- gets (S.member i . view checkedNodes)
      unless checked $ do
        st <- gets (fromMaybe M.empty . (M.!? i) . view states)
        forM_ (edgesFrom i aastg) $ \edge -> do
          let throwErr = throwError (TypeCheckError i (fromString $ show edge))
          case checkEdgeAndUpdate edge st of
            Nothing -> throwErr
            Just nt -> do
              let e = endNode edge
              mnt <- gets ((M.!? e) . view states)
              case mnt of
                Nothing              -> modify $ over states $ M.insert e nt
                Just nt' | nt /= nt' -> throwErr
                _                    -> return ()
              checking e

-- | Given the edge and its outgoing state's type, check if the edge can indeed go from the outgoing state, and generate the next state's type.
checkEdgeAndUpdate :: Edge sig c -> StateType -> Maybe StateType
checkEdgeAndUpdate = \case
  Update s e k a ->
    Just . M.insert (getPKeyID k) (typeRep k)   -- Haskell type system guarantees a to be the same in (k :: PKey a) and (a :: Attribute a)
  Forget s e k   ->
    Just . M.delete (getPKeyID k)
  Assert s e x y -> \st -> do
    tx <- st M.!? getPKeyID x
    ty <- st M.!? getPKeyID y
    if tx == ty then return st else Nothing
  APICall s e mx api args -> \st ->
    if not (attrsCheck args st)
      then Nothing
      else case mx of
        Nothing -> return st
        Just k  -> return (M.insert (getPKeyID k) (typeRep k) st)
    where
      attrsCheck :: (All Fuzzable a) => Attributes a -> StateType -> Bool
      attrsCheck Nil _ = True
      attrsCheck (a :* as) st = attrCheck a st && attrsCheck as st

      attrCheck :: (Fuzzable a) => Attribute a -> StateType -> Bool
      attrCheck = \case
        Get k -> \st -> fromMaybe False $ do
          tk <- st M.!? getPKeyID k
          return True
        AnyOf attrs -> \st -> all (`attrCheck` st) attrs
        _ -> const True

      args2TR :: (All Fuzzable a) => Attributes a -> [TypeRep]
      args2TR Nil = []
      args2TR (a :* as) = typeRep a : args2TR as

