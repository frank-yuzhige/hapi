{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Test.HAPI.Constraint where
import Data.Kind (Constraint, Type)

type family (c :: Type -> Constraint) :>>>: (ts :: [Type]) :: Constraint where
  c :>>>: '[] = ()
  c :>>>: (x : xs) = (c x, c :>>>: xs)

type family (cs :: [Type -> Constraint]) :>>>>: (ts :: [Type]) :: Constraint where
  '[]      :>>>>: xs = ()
  (c : cs) :>>>>: xs = (c :>>>: xs, cs :>>>>: xs)
