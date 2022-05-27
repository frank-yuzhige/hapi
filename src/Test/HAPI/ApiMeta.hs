{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Test.HAPI.ApiMeta where
import Data.Kind (Type)
import Data.TypeRepMap (TypeRepMap)
import Test.HAPI.Api (ApiDefinition)
import qualified Data.TypeRepMap as TM
import Data.Data (Typeable)


