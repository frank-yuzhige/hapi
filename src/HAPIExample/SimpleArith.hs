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

module HAPIExample.SimpleArith where
import Test.HAPI.Api (ApiDefinition, HasForeignDef (evalForeign))
import Foreign.C (CInt (CInt))
import Data.Data (Typeable)
import Test.HAPI.Args (args, Attribute (Anything, Get))
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Test.HAPI.AASTG.Core (AASTG)
import Test.HAPI.Effect.Eff (runEnv, runEnvIO, debug, debugIO)
import Test.HAPI.AASTG.Effect.Build (runBuildAASTG, Building (Building), (%>), val, var, call, vcall, fork)
import Test.HAPI.Common (Fuzzable)
import Data.SOP (NP(Nil, (:*)))
import Test.HAPI.AASTG.Analysis.Coalesce (coalesceAASTG, coalesceAASTGs)
import Test.HAPI.AASTG.GraphViz (previewAASTG)
import Test.HAPI.AASTG.Analysis.Rename (normalizeNodes)

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
  Neg :: ArithApi '[Int, Int] Int

deriving instance Typeable (ArithApi p a)
deriving instance Show     (ArithApi p a)
deriving instance Eq       (ArithApi p a)

instance HasForeignDef ArithApi where
  evalForeign Add [args|a b|] = fromIntegral <$> liftIO (add (fromIntegral a) (fromIntegral b))
  evalForeign Sub [args|a b|] = fromIntegral <$> liftIO (sub (fromIntegral a) (fromIntegral b))
  evalForeign Mul [args|a b|] = fromIntegral <$> liftIO (mul (fromIntegral a) (fromIntegral b))
  evalForeign Neg [args|a b|] = fromIntegral <$> liftIO (neg (fromIntegral a))

p :: Building ArithApi Fuzzable
p = Building

graph1 :: AASTG ArithApi Fuzzable
graph1 = runEnv $ runBuildAASTG $ do
  a <- val @Int 10  $ p
  b <- var @Int Anything $ p
  return ()
  -- call Add (Get a :* Get b :* Nil) $ p

graph2 :: AASTG ArithApi Fuzzable
graph2 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  return ()
  -- call Add (Get a :* Get b :* Nil) $ p
  where p = Building @ArithApi @Fuzzable

graph3 :: AASTG ArithApi Fuzzable
graph3 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  c <- vcall Add (Get a :* Get b :* Nil) $ p
  call Add (Get a :* Get c :* Nil) $ p

graph4 :: AASTG ArithApi Fuzzable
graph4 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  c <- vcall Add (Get a :* Get b :* Nil) $ p
  d <- vcall Add (Get a :* Get c :* Nil) $ p
  call Add (Get c :* Get d :* Nil) $ p

graph5 :: AASTG ArithApi Fuzzable
graph5 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  c <- vcall Add (Get a :* Get b :* Nil) $ p
  d <- vcall Sub (Get a :* Get c :* Nil) $ p
  call Add (Get c :* Get d :* Nil) $ p


graph6 :: AASTG ArithApi Fuzzable
graph6 = runEnv $ runBuildAASTG $ do
  a <- var (Anything @Int) $ p
  b <- var (Anything @Int) $ p
  c <- vcall Add (Get a :* Get b :* Nil) $ p
  d <- vcall Add (Get a :* Get c :* Nil) $ p
  fork p $ call Add (Get c :* Get d :* Nil) $ p
  call Mul (Get a :* Get d :* Nil) $ p

op :: AASTG api c -> AASTG api c -> IO (AASTG api c)
op g1 g2 = runEnvIO @IO $ do
  (h, c2) <- coalesceAASTG 5 g1 g2
  debug   $ show h
  let c2' = normalizeNodes 0 c2
  debugIO $ previewAASTG c2'
  debug   $ "Renaming"
  return c2'

c1 = op graph1 graph2
c2 = c1 >>= \g -> op g graph3
c3 = c2 >>= \g -> op g graph4
c4 = c3 >>= \g -> op g graph5

-- c2 = runEnv $ coalesceAASTG 500 (snd c1) graph3
-- c3 = snd $ runEnv $ coalesceAASTG 500 (snd c2) graph4

cograph :: AASTG ArithApi Fuzzable
cograph = runEnv $ coalesceAASTGs 500 [graph1, graph2, graph3, graph4, graph5, graph6]

previewCo :: IO ()
previewCo = previewAASTG cograph
