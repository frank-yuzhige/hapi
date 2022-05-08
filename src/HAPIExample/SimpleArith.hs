{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant $" #-}
{-# LANGUAGE TypeOperators #-}

module HAPIExample.SimpleArith where

import Test.HAPI
import Foreign.C (CInt (CInt), CString(..), CSize(..))
import Data.Data (Typeable)
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.SOP (NP(Nil, (:*)))
import qualified Data.ByteString as BS
import Test.QuickCheck (Arbitrary)
import Control.Monad (forM_, join)
import qualified Test.HAPI.PState as PS
import qualified Test.HAPI.VPtr as VP
import Test.HAPI.DataType (BasicSpec)
import Test.HAPI.PrimApi (Prim)
import qualified Test.HAPI.HLib.HLibPrelude as HLib
import Test.HAPI.HLib.HLibPrelude (HLibPrelude)
import Test.HAPI.AASTG.Analysis.Cycle (unrollCycle)
import qualified Data.IntMap as IM
import Control.Carrier.NonDet.Church (runNonDet)
import Control.Applicative (liftA2)
import Data.Hashable (hash)

foreign import ccall "broken_add"
  add :: CInt -> CInt -> IO CInt
foreign import ccall "segfault_minus"
  sub :: CInt -> CInt -> IO CInt
foreign import ccall "stateful_multiply"
  mul :: CInt -> CInt -> IO CInt
foreign import ccall "limited_input_range_negate"
  neg :: CInt -> IO CInt

data ArithApi :: ApiDefinition where
  Add :: ArithApi '[Int, Int] Int
  Sub :: ArithApi '[Int, Int] Int
  Mul :: ArithApi '[Int, Int] Int
  Neg :: ArithApi '[Int] Int

deriving instance Typeable (ArithApi p a)
deriving instance Show     (ArithApi p a)
deriving instance Eq       (ArithApi p a)
instance ApiName  ArithApi

instance HasForeignDef ArithApi where
  -- evalForeign Add [args|a b|] = fromIntegral <$> liftIO (add (fromIntegral a) (fromIntegral b))
  evalForeign Add = implE $ \a b -> fromIntegral <$> liftIO (add (fromIntegral a) (fromIntegral b))
  evalForeign Sub = implE $ \a b -> fromIntegral <$> liftIO (sub (fromIntegral a) (fromIntegral b))
  evalForeign Mul = implE $ \a b -> fromIntegral <$> liftIO (mul (fromIntegral a) (fromIntegral b))
  evalForeign Neg = implE $ \a   -> fromIntegral <$> liftIO (neg (fromIntegral a))


type A = ArithApi :$$: HLibPrelude

graph1 :: forall c. BasicSpec c => AASTG A c
graph1 = runEnv $ runBuildAASTG $ do
  a <- p <%> val @Int 10
  b <- p <%> var @Int Anything
  p <%> call Add (Get a, Get b)
  where p = Building @A @c

graph2 :: forall c. BasicSpec c => AASTG A c
graph2 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  p <%> call Add (Get a, Get b)
  where p = Building @A @c

graph3 :: forall c. BasicSpec c => AASTG A c
graph3 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  c <- p <%> vcall Add (Get b, Get a)
  p <%> call Add (Get a, Get c)
  where p = Building @A @c

graph4 :: forall c. BasicSpec c => AASTG A c
graph4 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  c <- p <%> vcall Add (Get a, Get b)
  d <- p <%> vcall Add (Get a, Get c)
  p <%> call Add (Get c, Get d)
  where p = Building @A @c

graph5 :: forall c. BasicSpec c => AASTG A c
graph5 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  c <- p <%> vcall Add (Get a, Get b)
  d <- p <%> vcall Sub (Get a, Get c)
  p <%> call Add (Get c, Get d)
  where p = Building @A @c

graph6 :: forall c. BasicSpec c => AASTG A c
graph6 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  c <- p <%> vcall Add (Get a, Get b)
  d <- p <%> vcall Add (Get a, Get c)
  fork p $ p <%> call Neg (Get c)
  fork p $ p <%> call (HLib.+) (Get c, Get c)
  p <%> call Mul (Get a, Get d)
  where p = Building @A @c

cograph :: forall c. BasicSpec c => AASTG A c
cograph = runEnv $ coalesceAASTGs 500 [graph1, graph2, graph3, graph4, graph5, graph6]

diamond :: forall c. BasicSpec c => AASTG A c
diamond = runEnv $ runBuildAASTG $ do
  n1 <- currNode @A @c
  n2 <- newNode @A @c
  n3 <- newNode @A @c
  n4 <- newNode @A @c
  n5 <- newNode @A @c
  x <- p <%(n1,n2)%> var Anything
  p <%(n2,n3)%> call Add (Get x, Value 1)
  p <%(n3,n5)%> call Add (Get x, Value 2)
  p <%(n2,n4)%> call Add (Get x, Value 3)
  p <%(n4,n5)%> call Add (Get x, Value 4)
  where p = Building @A @c


cyc :: forall c. BasicSpec c => AASTG A c
cyc = runEnv $ runBuildAASTG $ do
  n1 <- currNode @A @c
  n2 <- newNode @A @c
  n3 <- newNode @A @c
  n4 <- newNode @A @c
  n5 <- newNode @A @c
  x  <- p <%(n1,n2)%> var Anything
  p <%(n4,n3)%> call Add (Get x, Value 4)
  p <%(n3,n4)%> call Add (Get x, Value 2)
  p <%(n4,n2)%> call Add (Get x, Value 3)
  p <%(n2,n3)%> call Add (Get x, Value 1)
  where p = Building @A @c

  -- newEdge @A @c (Redirect n2 n5)

cyc2 :: forall c. BasicSpec c => AASTG A c
cyc2 = runEnv $ runBuildAASTG $ do
  n1 <- currNode @A @c
  n2 <- newNode @A @c
  n3 <- newNode @A @c
  n4 <- newNode @A @c
  x <- p <%(n1,n2)%> var Anything
  p <%(n2,n3)%> call Add (Get x, Value 1)
  p <%(n3,n4)%> call Add (Get x, Value 2)
  p <%(n4,n2)%> call Add (Get x, Value 3)
  where p = Building @A @c

cyc3 :: forall c. BasicSpec c => AASTG A c
cyc3 = runEnv $ runBuildAASTG $ do
  n1 <- currNode @A @c
  n2 <- newNode @A @c
  n3 <- newNode @A @c
  n4 <- newNode @A @c
  x <- p <%(n1,n2)%> var Anything
  p <%(n2,n3)%> call Add (Get x, Value 1)
  p <%(n3,n4)%> call Sub (Get x, Value 2)
  p <%(n4,n2)%> call Add (Get x, Value 3)
  p <%(n4,n3)%> call Add (Get x, Value 4)
  p <%(n4,n3)%> call Add (Get x, Value 5)
  where p = Building @A @c

op :: ApiName api => AASTG api c -> AASTG api c -> IO (AASTG api c)
op = op' 1000

op' :: ApiName api => Int -> AASTG api c -> AASTG api c -> IO (AASTG api c)
op' n g1 g2 = runEnvIO @IO $ do
  (h, c2) <- coalesceAASTG n g1 g2
  debug   $ show h
  return c2


-- c1 = op graph1 graph2
-- c2 = c1 >>= \g -> op g graph3
-- c3 = c2 >>= \g -> op g graph4
-- c4 = c3 >>= \g -> op g graph5
-- c5 = c4 >>= \g -> op' 5 g graph6


previewCo :: IO ()
previewCo = previewAASTG (cograph @Fuzzable)

previewCy = previewAASTG (cyc @Fuzzable)

previewD = do
  let a = cyc3 @Fuzzable
      b = cyc @Fuzzable
  previewAASTG a
  previewAASTG b
  previewAASTG =<< op' 0 a b
  previewAASTG =<< op' 1 a b
  x <- op' 2 a b
  previewAASTG x
  previewAASTG =<< op' 3 a b
  previewAASTG =<< op' 4 a b

q = do
  x <- runEnvIO @IO (inferProcType test)
  print x
  previewAASTG test
  where
    test = cyc @Fuzzable
-- test = do
--   previewAASTG graph6
--   c4 >>= previewAASTG
--   c5 >>= previewAASTG
--   -- previewCo

-- runGraph1 :: forall m sig. (MonadIO m, MonadFail m, Alg sig m) => m ()
-- runGraph1 = do
--   let s = synthStub cograph
--   debug $ show (length s)
--   debug $ show (length (outPaths 0 cograph))
--   forM_ s $ \stub -> do id
--        . runGenIO
--        . runError @PropertyError (fail . show) pure
--        . runProperty @PropertyA
--        . runWriter @(ApiTrace ArithApi)
--        . runTrace
--        . runForeign (fail . show)
--        . runApiFFI @ArithApi
--        . runState (\s a -> return a) PS.empty
--        . runQVSFuzzArbitraryAC
--        $ stub

-- gogo :: IO ()
-- gogo = runEnvIO runGraph1

-- foreign export ccall "LLVMFuzzerTestOneInput" testOneInputM
--     :: CString -> CSize -> IO CInt

-- testOneInputM :: CString -> CSize -> IO CInt
-- testOneInputM str size = do
--   bs <- BS.packCStringLen (str, fromIntegral size)
--   return 0
