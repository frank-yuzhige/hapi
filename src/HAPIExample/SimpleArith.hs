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
{-# HLINT ignore "Use let" #-}
{-# LANGUAGE ConstraintKinds #-}

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
import Test.HAPI.AASTG.Analysis.ProcCtx (deriveProcCtxs)
import Control.Carrier.Error.Church (runError)
import Language.C (Pretty(pretty))

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
instance ApiName  ArithApi where
  apiNameUnder "C" Add = "broken_add"
  apiNameUnder "C" Sub = "segfault_minus"
  apiNameUnder "C" Mul = "stateful_multiply"
  apiNameUnder "C" Neg = "limited_input_range_negate"
  apiNameUnder _   a   = apiName a

instance Entry2BlockC ArithApi

instance HasForeignDef ArithApi where
  -- evalForeign Add [args|a b|] = fromIntegral <$> liftIO (add (fromIntegral a) (fromIntegral b))
  evalForeign Add = implE $ \a b -> fromIntegral <$> liftIO (add (fromIntegral a) (fromIntegral b))
  evalForeign Sub = implE $ \a b -> fromIntegral <$> liftIO (sub (fromIntegral a) (fromIntegral b))
  evalForeign Mul = implE $ \a b -> fromIntegral <$> liftIO (mul (fromIntegral a) (fromIntegral b))
  evalForeign Neg = implE $ \a   -> fromIntegral <$> liftIO (neg (fromIntegral a))


type A = ArithApi :$$: HLibPrelude
type C = Fuzzable :<>: CCodeGen


graph1 :: forall c. BasicSpec c => AASTG A c
graph1 = runEnv $ runBuildAASTG $ do
  a <- p <%> val @Int 10
  b <- p <%> var @Int Anything
  p <%> call Add (getVar a, getVar b)
  where p = Building @A @c

graph2 :: forall c. BasicSpec c => AASTG A c
graph2 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  p <%> call Add (getVar a, getVar b)
  where p = Building @A @c

graph3 :: forall c. BasicSpec c => AASTG A c
graph3 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  c <- p <%> call Add (getVar b, getVar a)
  p <%> call Add (getVar a, getVar c)
  where p = Building @A @c

graph4 :: forall c. BasicSpec c => AASTG A c
graph4 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  c <- p <%> call Add (getVar a, getVar b)
  d <- p <%> call Add (getVar a, getVar c)
  p <%> call Add (getVar c, getVar d)
  where p = Building @A @c

graph5 :: forall c. BasicSpec c => AASTG A c
graph5 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  c <- p <%> call Add (getVar a, getVar b)
  d <- p <%> call Sub (getVar a, getVar c)
  p <%> call Add (getVar c, getVar d)
  where p = Building @A @c

graph6 :: forall c. BasicSpec c => AASTG A c
graph6 = runEnv $ runBuildAASTG $ do
  a <- p <%> var (Anything @Int)
  b <- p <%> var (Anything @Int)
  c <- p <%> call Add (getVar a, getVar b)
  d <- p <%> call Add (getVar a, getVar c)
  fork p $ p <%> call Neg (getVar c)
  fork p $ p <%> call (HLib.+) (getVar c, getVar c)
  p <%> call Mul (getVar a, getVar d)
  where p = Building @A @c

cograph :: forall c. BasicSpec c => AASTG A c
cograph = runEnv $ coalesceAASTGs 500 [graph1, graph2, graph3, graph4, graph5, graph6]

diamond :: forall c. BasicSpec c => AASTG A c
diamond = runEnv $ runBuildAASTG $ do
  n1 <- p <%> currNode
  n2 <- p <%> newNode
  n3 <- p <%> newNode
  n4 <- p <%> newNode
  n5 <- p <%> newNode
  x <- p <%(n1,n2)%> var Anything
  p <%(n2,n3)%> call Add (getVar x, value 1)
  p <%(n3,n5)%> call Add (getVar x, value 2)
  p <%(n2,n4)%> call Add (getVar x, value 3)
  p <%(n4,n5)%> call Add (getVar x, value 4)
  where p = Building @A @c


cyc :: forall c. BasicSpec c => AASTG A c
cyc = runEnv $ runBuildAASTG $ do
  n1 <- p <%> currNode
  n2 <- p <%> newNode
  n3 <- p <%> newNode
  n4 <- p <%> newNode
  n5 <- p <%> newNode
  n6 <- p <%> newNode
  x  <- p <%(n1,n2)%> var Anything
  p <%(n4,n3)%> call Add (getVar x, value 4)
  p <%(n3,n4)%> call Add (getVar x, value 2)
  p <%(n4,n2)%> call Add (getVar x, value 3)
  p <%(n2,n3)%> call Add (getVar x, value 1)
  b  <- p <%(n4, n5)%> call (HLib.==) (getVar x, value 10)
  p <%(n5, n6)%> assert b
  where p = Building @A @c

  -- newEdge @A @c (Redirect n2 n5)

cyc2 :: forall c. BasicSpec c => AASTG A c
cyc2 = runEnv $ runBuildAASTG $ do
  n1 <- p <%> currNode
  n2 <- p <%> newNode
  n3 <- p <%> newNode
  n4 <- p <%> newNode
  x <- p <%(n1,n2)%> var Anything
  p <%(n2,n3)%> call Add (getVar x, value 1)
  p <%(n3,n4)%> call Add (getVar x, value 2)
  p <%(n4,n2)%> call Add (getVar x, value 3)
  where p = Building @A @c

cyc3 :: forall c. BasicSpec c => AASTG A c
cyc3 = runEnv $ runBuildAASTG $ do
  n1 <- p <%> currNode
  n2 <- p <%> newNode
  n3 <- p <%> newNode
  n4 <- p <%> newNode
  x <- p <%(n1,n2)%> var Anything
  p <%(n2,n3)%> call Add (getVar x, value 1)
  p <%(n3,n4)%> call Sub (getVar x, value 2)
  p <%(n4,n2)%> call Add (getVar x, value 3)
  p <%(n4,n3)%> call Add (getVar x, value 4)
  p <%(n4,n3)%> call Add (getVar x, value 5)
  where p = Building @A @c

cyc4 :: forall c. BasicSpec c => AASTG A c
cyc4 = runEnv $ runBuildAASTG $ do
  n1 <- p <%> currNode
  n2 <- p <%> newNode
  n3 <- p <%> newNode
  x <- p <%(n1,n2)%> var Anything
  p <%(n2,n3)%> call Add (getVar x, value 1)
  p <%(n3,n2)%> call Sub (getVar x, value 2)
  where p = Building @A @c

invalid :: forall c. BasicSpec c => AASTG A c
invalid = runEnv $ runBuildAASTG $ do
  n1 <- p <%> currNode
  n2 <- p <%> newNode
  n3 <- p <%> newNode
  n4 <- p <%> newNode
  x <- p <%(n1,n2)%> var Anything
  y <- p <%(n3,n2)%> call Sub (getVar x, value 2)
  p <%(n2,n3)%> call Add (getVar x, getVar y)
  p <%(n2,n4)%> assertTrue (HLib.==) (getVar x, getVar y)
  where p = Building @A @c


addComp :: AASTG A C
addComp = runEnv $ runBuildAASTG $ do
  -- p <%> redirect

  s <- p <%> currNode
  a <- p <%> var @Int Anything
  b <- p <%> var @Int Anything
  x <- p <%> call Add (getVar a, getVar b)
  y <- p <%> call (HLib.+) (getVar a, getVar b)
  p <%> assertTrue (HLib.==) (getVar x, getVar y)
  -- s' <- p <%> currNode
  -- p <%(s', s)%> redirect
  where p = Building @A @C


op :: ApiName api => AASTG api c -> AASTG api c -> IO (AASTG api c)
op = op' 1000

op' :: ApiName api => Int -> AASTG api c -> AASTG api c -> IO (AASTG api c)
op' n g1 g2 = runEnvIO @IO $ do
  (h, c2) <- coalesceAASTG n g1 g2
  debug   $ show h
  return c2


addAssoc :: AASTG A C
addAssoc = runEnv $ runBuildAASTG $ do
  -- p <%> redirect
  s <- p <%> currNode
  a <- p <%> var @Int Anything
  b <- p <%> var @Int Anything
  x <- p <%> call Add (getVar a, getVar b)
  y <- p <%> call Add (getVar b, getVar a)
  p <%> assertTrue (HLib.==) (getVar x, getVar y)
  -- s' <- p <%> currNode
  -- p <%(s', s)%> redirect
  where p = Building @A @C

addAssoc2 :: AASTG A C
addAssoc2 = runEnv $ runBuildAASTG $ do
  -- p <%> redirect
  s <- p <%> currNode
  a <- p <%> var @Int Anything
  b <- p <%> var @Int Anything
  x <- p <%> call Add (getVar b, getVar a)
  y <- p <%> call Add (getVar a, getVar b)
  p <%> assertTrue (HLib.==) (getVar x, getVar y)
  -- s' <- p <%> currNode
  -- p <%(s', s)%> redirect
  where p = Building @A @C

mulAssoc :: AASTG A C
mulAssoc = runEnv $ runBuildAASTG $ do
  p <%> redirect
  s <- p <%> currNode
  a <- p <%> var @Int Anything
  b <- p <%> var @Int Anything
  x <- p <%> call Mul (getVar a, getVar b)
  y <- p <%> call Mul (getVar b, getVar a)
  p <%> assertTrue (HLib.==) (getVar x, getVar y)
  s' <- p <%> currNode
  p <%(s', s)%> redirect
  where p = Building @A @C

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
  test <- return (cyc3 @C) -- runEnvIO $ coalesceAASTGs 500 [addAssoc, addComp, addAssoc2, mulAssoc]
  previewAASTG test
  n <- runEnvIO @IO $ inferProcTypeUB test
  x <- runEnvIO @IO $ runError @TypeCheckError (return . Left) (return . Right) (typeCheck test)
  let v = acyclicNodes n
  print n
  print v
  print x
  -- print v
  -- y <- runEnvIO @IO $ deriveProcCtxs x
  -- print y

shite = pretty $ entryFun @ArithApi @(CCodeGen :<>: Fuzzable) "main" (traceCall (PKey "x") Add (Value 10 :* Value 20 :* Nil))

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
