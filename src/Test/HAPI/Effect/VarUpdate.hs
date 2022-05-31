{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.Effect.VarUpdate where
import Data.Kind (Type, Constraint)
import Test.HAPI.Args (DirectAttribute, evalDirect')
import Test.HAPI.Common (Fuzzable, ErrorMsg)
import Test.HAPI.PState ( PKey(..), PState(..), record )
import Control.Monad.IO.Class (MonadIO)
import Control.Algebra (Algebra(..), Has, type (:+:) (..))
import Control.Effect.State (State, get, modify)
import Control.Effect.Error (Error, throwError)
import Data.Functor (($>))
import Control.Effect.Writer (Writer, tell)
import Test.HAPI.ApiTrace.Core ( ApiTrace )
import Test.HAPI.ApiTrace.Core (traceDirect)
import Test.HAPI.Api (ApiDefinition)


data VarUpdate (api :: ApiDefinition) (c :: Type -> Constraint) (m :: Type -> Type) a where
  VarUpdate :: (Fuzzable a, c a) => PKey a -> DirectAttribute c a -> VarUpdate api c m ()

data VarUpdateError = VarUpdateError { errorVar :: String, varErrorCause :: ErrorMsg }
  deriving (Show)


data VUEval  (api :: ApiDefinition) (c :: Type -> Constraint)
data VUTrace (api :: ApiDefinition) (c :: Type -> Constraint)


newtype VarUpdateCA proxy m a = VarUpdateCA { runVarUpdateCA :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runVarUpdateEval :: VarUpdateCA (VUEval api c) m a -> m a
runVarUpdateEval = runVarUpdateCA

runVarUpdateTrace :: VarUpdateCA (VUTrace api c) m a -> m a
runVarUpdateTrace = runVarUpdateCA

instance ( Algebra sig m
         , Has (State PState) sig m
         , Has (Error VarUpdateError) sig m)
      => Algebra (VarUpdate api c :+: sig) (VarUpdateCA (VUEval api c) m) where
  alg hdl sig ctx = VarUpdateCA $ case sig of
    L (VarUpdate k d) -> do
      s <- get @PState
      case evalDirect' s d of
        Left err -> throwError (VarUpdateError (show k) err)
        Right  v -> do
          modify @PState (record k v)
          return (ctx $> ())
    R other           -> alg (runVarUpdateCA . hdl) other ctx


instance ( Algebra sig m
         , Has (State PState) sig m
         , Has (Error VarUpdateError) sig m
         , Has (Writer (ApiTrace api c)) sig m)
      => Algebra (VarUpdate api c :+: sig) (VarUpdateCA (VUTrace api c) m) where
  alg hdl sig ctx = VarUpdateCA $ case sig of
    L (VarUpdate k d) -> do
      tell (traceDirect @api @c k d)
      return (ctx $> ())
    R other           -> alg (runVarUpdateCA . hdl) other ctx
