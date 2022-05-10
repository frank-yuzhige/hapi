{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}

module Test.HAPI.AASTG.Analysis.ProcCtx where

import Data.HashSet (HashSet)


import Test.HAPI.PState (PKey (getPKeyID))
import Test.HAPI.AASTG.Analysis.ProcType ( ProcType (..), Action (..), SVar, ProcTypeMap, UnboundedProcTypeMap (..) )
import Data.HashMap.Strict (HashMap)

import qualified Test.HAPI.Util.TypeRepMap as TM
import qualified Data.HashMap.Strict as HM
import Test.HAPI.Effect.Eff (Eff, Alg, debug)
import Control.Effect.State (State, gets, modify)
import Data.Data (Typeable)
import qualified Data.HashSet as HS
import Control.Carrier.State.Church (runState)
import Control.Monad (forM)
import qualified Data.IntMap as IM
import Data.IntMap (IntMap)
import Text.Printf (printf)
import Data.List (intercalate, sort)


-- | The context of a procedure type is the set of variables that is safe to be used in the subsequent procedure.


type ProcCtxMap = IntMap ProcCtx

type ProcCtxQueries = IntMap ProcCtxQuery

newtype PCE k = PCE { unPCE :: HashSet (PKey k) }  -- ProcCtxEntry
  deriving (Eq, Show)

-- Defintion of procedure type context
data ProcCtx
  = Finite (TM.TypeRepMap PCE)
  | Infinite
  deriving (Eq)

-- Query for inferring procedure type context from procedure type
data ProcCtxQuery
  = PCtx       ProcCtx
  | PSVar      SVar
  | PIntersect ProcCtxQuery ProcCtxQuery
  | PUnion     ProcCtxQuery ProcCtxQuery
  deriving (Eq, Show)


-- | ProcCtx Utils

singletonCtx :: Typeable t => PKey t -> ProcCtx
singletonCtx k = addPKey2Ctx k (Finite TM.empty)

addPKey2Ctx :: Typeable t => PKey t -> ProcCtx -> ProcCtx
addPKey2Ctx k Infinite    = Infinite
addPKey2Ctx k (Finite pc) = case TM.lookup pc of
  Nothing      -> Finite $ TM.insert (PCE (HS.singleton k)) pc
  Just (PCE s) -> Finite $ TM.insert (PCE (HS.insert k s )) pc

dropPKeyInCtx :: Typeable t => PKey t -> ProcCtx -> ProcCtx
dropPKeyInCtx k Infinite    = Infinite
dropPKeyInCtx k (Finite pc) = case TM.lookup pc of
  Nothing      -> Finite pc
  Just (PCE s) -> Finite $ TM.insert (PCE (HS.delete k s)) pc

memberCtx :: Typeable t => PKey t -> ProcCtx -> Bool
memberCtx k Infinite    = True
memberCtx k (Finite pc) = case TM.lookup pc of
  Nothing      -> False
  Just (PCE s) -> HS.member k s

intersectCtx :: ProcCtx -> ProcCtx -> ProcCtx
intersectCtx (Finite c1) (Finite c2) = Finite $ TM.intersectionWith intersectPCE c1 c2
  where
    intersectPCE (PCE s1) (PCE s2) = PCE (s1 `HS.intersection` s2)
intersectCtx Infinite c2       = c2
intersectCtx c1       Infinite = c1

intersectCtxs :: [ProcCtx] -> ProcCtx
intersectCtxs []       = Finite TM.empty
intersectCtxs (c : cs) = foldr intersectCtx c cs

unionCtx :: ProcCtx -> ProcCtx -> ProcCtx
unionCtx (Finite c1) (Finite c2) = Finite $ TM.unionWith unionPCE c1 c2
  where
    unionPCE (PCE s1) (PCE s2) = PCE (s1 `HS.union` s2)
unionCtx _           _           = Infinite

-- | Derive ProcCtx from the given (well-formed) ProcType
deriveProcCtx ::
               ( Alg sig m )
            => ProcType
            -> m ProcCtx
deriveProcCtx t = do
  (q, qs) <- runState @ProcCtxQueries (\s a -> return (a, s)) IM.empty $ genProcQuery t
  -- debug $ printf "%s: Query: %s;    Queries: %s" (show 'deriveProcCtx) (show q) (show qs)
  let st = solveProcQueries qs
  return $ solveProcQuery st q

-- | Derive all ProcCtx from the given (well-formed) ProcType map
--   TODO: Optimization (Unboundeded type to simply calculation?) (Memoize query results?)
deriveProcCtxs ::
                ( Alg sig m )
             => ProcTypeMap
             -> m ProcCtxMap
deriveProcCtxs ptm = do
  es <- forM (IM.assocs ptm) $ \(n, t) -> do
    ctx <- deriveProcCtx t
    return (n, ctx)
  return $ IM.fromList es

deriveProcCtxsUB ::
                  ( Alg sig m )
               => UnboundedProcTypeMap
               -> m ProcCtxMap
deriveProcCtxsUB (UnboundedProcTypeMap uptm) = do
  queries <- fmap IM.unions $ forM (IM.assocs uptm) $ \(n, t) -> do
    (q, qs) <- runState @ProcCtxQueries (\s a -> return (a, s)) IM.empty $ genProcQuery t
    return $ IM.insert n q qs
  debug $ printf "%s: Queries: %s" (show 'deriveProcCtxsUB) (show queries)
  return $ IM.fromList [(n, solveProcQueries queries IM.! n)| n <- IM.keys uptm]

-- | Generate ProcCtx queries from the given type, return the query for solving the given type's context
genProcQuery ::
              ( Eff (State ProcCtxQueries) sig m )
           => ProcType
           -> m ProcCtxQuery
genProcQuery = \case
  SVar x                  -> return (PSVar x)
  Act  (ActGen  k _)   t' -> PUnion (PCtx (singletonCtx k)) <$> genProcQuery t'
  Act  (ActCall k _ _) t' -> PUnion (PCtx (singletonCtx k)) <$> genProcQuery t'
  Par  ts                 -> intersectQueries <$> mapM genProcQuery ts
  Mu x t'                 -> do
    q <- genProcQuery t'
    modify (IM.insert x q)
    return (PSVar x)
  Zero                    -> return $ PCtx $ Finite TM.empty
  where
    intersectQueries []       = PCtx Infinite
    intersectQueries [a]      = a
    intersectQueries (a : as) = foldr PIntersect a as

-- | Solve a single query using the SVar -> ProcCtx substitution
solveProcQuery :: ProcCtxMap -> ProcCtxQuery -> ProcCtx
solveProcQuery st = \case
  PCtx       c   -> c
  PSVar      x   -> st IM.! x
  PIntersect a b -> intersectCtx (solveProcQuery st a) (solveProcQuery st b)
  PUnion     a b -> unionCtx     (solveProcQuery st a) (solveProcQuery st b)

-- | Solve multiple queries to generate the SVar -> ProcCtx mapping, via an iterative algoritIM.
--   TODO: Optimization (Worklist?)
solveProcQueries :: ProcCtxQueries -> ProcCtxMap
solveProcQueries qs = iter (IM.map (const Infinite) qs)
  where
    iter st
      | st == st' = st
      | otherwise = iter st'
      where
        st' = IM.map (solveProcQuery st) qs


instance Show ProcCtx where
  show Infinite   = "Infinite"
  show (Finite m) = "{" <> intercalate ", " (TM.toListWith (\(PCE pce) -> intercalate ", " (sort $ map getPKeyID $ HS.toList pce)) m) <> "}"
