{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-

Communication: HAPI Tester <-> HAPI wrapper

-}

module Test.HAPI.Comm where

import Control.Algebra (Has, alg, send, Algebra, (:+:) (L, R))
import Control.Carrier.State.Church (StateC)
import Control.Monad.IO.Class (MonadIO)
