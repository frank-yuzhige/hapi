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
import Data.GraphViz.Types.Graph (addEdge)
import Test.HAPI.AASTG.Analysis.NodeDepType (inferNodeDepType, isST, isSubType)
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
  a <- val @Int 10  $ p
  b <- var @Int Anything $ p
  call Add (Get a :* Get b :* Nil) $ p
  where p = Building @A @c

graph2 :: forall c. BasicSpec c => AASTG A c
graph2 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  call Add (Get a :* Get b :* Nil) $ p
  where p = Building @A @c

graph3 :: forall c. BasicSpec c => AASTG A c
graph3 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  c <- vcall Add (Get b :* Get a :* Nil) $ p
  call Add (Get a :* Get c :* Nil) $ p
  where p = Building @A @c

graph4 :: forall c. BasicSpec c => AASTG A c
graph4 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  c <- vcall Add (Get a :* Get b :* Nil) $ p
  d <- vcall Add (Get a :* Get c :* Nil) $ p
  call Add (Get c :* Get d :* Nil) $ p
  where p = Building @A @c

graph5 :: forall c. BasicSpec c => AASTG A c
graph5 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  c <- vcall Add (Get a :* Get b :* Nil) $ p
  d <- vcall Sub (Get a :* Get c :* Nil) $ p
  call Add (Get c :* Get d :* Nil) $ p
  where p = Building @A @c

graph6 :: forall c. BasicSpec c => AASTG A c
graph6 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  c <- vcall Add (Get a :* Get b :* Nil) $ p
  d <- vcall Add (Get a :* Get c :* Nil) $ p
  fork p $ call Neg (Get c :* Nil) $ p
  fork p $ call (HLib.+) (Get c :* Get c :* Nil) $ p
  call Mul (Get a :* Get d :* Nil) $ p
  where p = Building @A @c

cograph :: forall c. BasicSpec c => AASTG A c
cograph = unrollCycle 200 $ runEnv $ coalesceAASTGs 500 [graph1, graph2, graph3, graph4, graph5, graph6]

diamond :: forall c. BasicSpec c => AASTG A c
diamond = runEnv $ runBuildAASTG $ do
  n1 <- currNode @A @c
  n2 <- newNode @A @c
  n3 <- newNode @A @c
  n4 <- newNode @A @c
  n5 <- newNode @A @c
  x  <- newVar  @A @c
  newEdge @A @c (Update n1 n2 x Anything)
  newEdge @A @c (APICall n2 n3 Nothing (injApi Add) (Get x :* Value 1 :* Nil))
  newEdge @A @c (APICall n3 n5 Nothing (injApi Add) (Get x :* Value 2 :* Nil))
  newEdge @A @c (APICall n2 n4 Nothing (injApi Add) (Get x :* Value 3 :* Nil))
  newEdge @A @c (APICall n4 n5 Nothing (injApi Add) (Get x :* Value 4 :* Nil))

cyc :: forall c. BasicSpec c => AASTG A c
cyc = runEnv $ runBuildAASTG $ do
  n1 <- currNode @A @c
  n2 <- newNode @A @c
  n3 <- newNode @A @c
  n4 <- newNode @A @c
  n5 <- newNode @A @c
  x  <- newVar  @A @c
  newEdge @A @c (Update n1 n2 x Anything)
  newEdge @A @c (APICall n2 n3 Nothing (injApi Add) (Get x :* Value 1 :* Nil))
  newEdge @A @c (APICall n3 n4 Nothing (injApi Add) (Get x :* Value 2 :* Nil))
  newEdge @A @c (APICall n4 n2 Nothing (injApi Add) (Get x :* Value 3 :* Nil))
  newEdge @A @c (APICall n4 n3 Nothing (injApi Add) (Get x :* Value 4 :* Nil))
  -- newEdge @A @c (Redirect n2 n5)

cyc2 :: forall c. BasicSpec c => AASTG A c
cyc2 = runEnv $ runBuildAASTG $ do
  n1 <- currNode @A @c
  n2 <- newNode @A @c
  n3 <- newNode @A @c
  n4 <- newNode @A @c
  x  <- newVar  @A @c
  newEdge @A @c (Update n1 n2 x Anything)
  newEdge @A @c (APICall n2 n3 Nothing (injApi Add) (Get x :* Value 1 :* Nil))
  newEdge @A @c (APICall n3 n4 Nothing (injApi Add) (Get x :* Value 2 :* Nil))
  newEdge @A @c (APICall n4 n2 Nothing (injApi Add) (Get x :* Value 3 :* Nil))

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
  let a = diamond @Fuzzable
      b = cyc @Fuzzable
  previewAASTG a
  previewAASTG b
  previewAASTG =<< op' 0 a b
  c <- op' 1 a b
  previewAASTG c
  -- x <- runEnvIO @IO (inferNodeDepType c)
  -- y <- runEnvIO @IO $ runNonDet fork (return . Just) (return Nothing) $ isSubType (x IM.! 5) (x IM.! 2)
  -- putStrLn "-----------"
  -- print y
  -- print (x IM.! 5)
  -- print (x IM.! 2)
  -- print (x IM.! 5 == x IM.! 2)
  -- print (hash (x IM.! 5), hash (x IM.! 2))
  previewAASTG =<< op' 2 a b




  -- previewAASTG =<< op' 3 a b

q = do
  x <- runEnvIO @IO (inferNodeDepType test)
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
