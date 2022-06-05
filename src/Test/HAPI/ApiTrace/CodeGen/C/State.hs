{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.ApiTrace.CodeGen.C.State where
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CBaseType, TyConstC (toCBType))
import Data.Set (Set)
import Control.Lens (makeLenses, view, over)
import Control.Algebra (Has)
import Control.Effect.State (State, modify)
import qualified Data.Set as S
import Data.SOP (All, Proxy (Proxy), NP (..))
import Test.HAPI.Constraint ((:>>>:), witnessC)
import Data.Constraint ((\\))

newtype CCodeGenState = CCodeGenState
 { _declBaseTypes :: Set CBaseType
 }

type HasCodeGenC sig m = Has (State CCodeGenState) sig m

$(makeLenses ''CCodeGenState)

emptyCCodeGenState :: CCodeGenState
emptyCCodeGenState = CCodeGenState S.empty

recordType :: (TyConstC t, HasCodeGenC sig m) => proxy t -> m ()
recordType p = modify $ over declBaseTypes $ S.insert (toCBType p)

recordTypes :: forall c p f sig m. (c :>>>: TyConstC, All c p, HasCodeGenC sig m) => NP f p -> m ()
recordTypes Nil                = return ()
recordTypes ((a :: f x) :* as) = recordType a \\ witnessC @TyConstC @c @x >> recordTypes @c as
