module Test.HAPI.AASTG.Analysis.Cycle where

import Test.HAPI.AASTG.Core ( AASTG (AASTG), NodeID, edgesFrom, endNode )
import Data.IntSet as IS
import Control.Carrier.State.Church (runState, run)
import Control.Effect.State (gets, State)
import Control.Algebra (Has)
import Control.Monad (forM)


isCyclicAASTG :: AASTG api c -> [NodeID]
isCyclicAASTG aastg@(AASTG s _ _) = run $ runState (\s a -> return a) IS.empty $ go s
  where
    go :: Has (State IntSet) sig m => Int -> m [NodeID]
    go i = do
      visited <- gets (IS.member i)
      if visited then return [i] else do
        fmap concat $ forM (edgesFrom i aastg) $
          \e -> go (endNode e)



-- acyclify :: Int -> AASTG api c -> AASTG api c
-- acyclify c aastg = _
--   where
--     expand 0 i = _
--     expand n i = _
