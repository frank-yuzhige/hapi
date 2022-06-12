{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.Conduct.Quickcheck where
import Test.QuickCheck (Arbitrary)
import Test.HAPI.Api (ValidApiDef, runForeign)
import Test.HAPI.Constraint (CMembers)
import Data.Data (Typeable)
import Test.HAPI.AASTG.Synth (synthEntropyStub, execEntropyFuzzerHandler, EntropyStubResult (..))
import Test.HAPI.Effect.Entropy (EntropyCounter, EntropyAGenC (..))
import Test.HAPI.Effect.Property (PropertyA)
import qualified Test.HAPI.PState as PS
import Test.HAPI.Effect.VarUpdate (VarUpdateError, runVarUpdateEval)
import Test.HAPI.Effect.Property (PropertyError)
import Test.HAPI.Effect.EVS (EVSError, EVSFuzzArbitraryAC (..))
import Control.Carrier.Error.Church (runError)
import Test.HAPI.Effect.Property (runProperty)
import Control.Carrier.State.Church (runState)
import Test.HAPI.Effect.Api (runApiFFI)
import Test.HAPI.AASTG.Effect.Trav (runTrav)
import Text.Printf (printf)
import Test.HAPI.Effect.Eff (debug, runEnvIO)
import qualified Control.Carrier.Trace.Printing as PRINTING
import Test.HAPI.AASTG.Core (AASTG)
import Test.HAPI.PState (PState)
import Test.HAPI.Effect.Gen (runGenIO)
import Control.Monad.IO.Class (MonadIO(liftIO))


newtype QuickCheckConduct = QuickCheckConduct
  { testM  :: IO ()
  }

quickCheckConduct :: ( ValidApiDef api
                     , CMembers Arbitrary c
                     , c Bool
                     , Typeable c)
                  => AASTG api c -> QuickCheckConduct
quickCheckConduct aastg = QuickCheckConduct
  { testM = runQuickCheckFuzz aastg
  }

runQuickCheckFuzz :: forall api c.
                   ( ValidApiDef api
                   , CMembers Arbitrary c
                   , c Bool
                   , Typeable c)
                => AASTG api c -> IO ()
runQuickCheckFuzz aastg = runEnvIO go
  where
   stub = synthEntropyStub @api @c aastg
   go = do
    liftIO $ printf "--------------------------\n"
    s <- runError @EVSError (return . Left . show) return
          $ runError @PropertyError  (fail . show) pure
          $ runError @VarUpdateError (fail . show) pure
          $ runGenIO
          $ runState @PState (\s a -> return a) PS.emptyPState
          $ runProperty @(PropertyA c)
          $ runForeign (return . Left . show) (return . Right)
          $ PRINTING.runTrace
          $ runApiFFI @api @c
          $ runVarUpdateEval @api @c
          $ runEVSFuzzArbitraryAC @c
          $ runState @EntropyCounter (\s a -> return a) 0
          $ runEntropyAGenC
          $ runTrav @api @c execEntropyFuzzerHandler stub
    case s of
      Left err -> liftIO (printf "error: %s\n" err ) >> go
      _        -> go
