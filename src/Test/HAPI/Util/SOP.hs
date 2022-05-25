{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Test.HAPI.Util.SOP where
import Data.SOP (NP (..))

class InjNP t f p | t f -> p, p f -> t where
  injNP :: t -> NP f p

-- instance InjNP (NP f p) f p where
--   injNP = id


instance InjNP () f '[] where
  injNP _ = Nil

instance InjNP (f a) f '[a] where
  injNP a = a :* Nil

instance InjNP (f a1, f a2) f '[a1, a2] where
  injNP (a1, a2) = a1 :* a2 :* Nil

instance InjNP (f a1, f a2, f a3) f '[a1, a2, a3] where
  injNP (a1, a2, a3) = a1 :* a2 :* a3 :* Nil

instance InjNP (f a1, f a2, f a3, f a4) f '[a1, a2, a3, a4] where
  injNP (a1, a2, a3, a4) = a1 :* a2 :* a3 :* a4 :* Nil

instance InjNP (f a1, f a2, f a3, f a4, f a5) f '[a1, a2, a3, a4, a5] where
  injNP (a1, a2, a3, a4, a5) = a1 :* a2 :* a3 :* a4 :* a5 :* Nil

instance InjNP (f a1, f a2, f a3, f a4, f a5, f a6) f '[a1, a2, a3, a4, a5, a6] where
  injNP (a1, a2, a3, a4, a5, a6) = a1 :* a2 :* a3 :* a4 :* a5 :* a6 :* Nil

instance InjNP (f a1, f a2, f a3, f a4, f a5, f a6, f a7) f '[a1, a2, a3, a4, a5, a6, a7] where
  injNP (a1, a2, a3, a4, a5, a6, a7) = a1 :* a2 :* a3 :* a4 :* a5 :* a6 :* a7 :* Nil

instance InjNP (f a1, f a2, f a3, f a4, f a5, f a6, f a7, f a8) f '[a1, a2, a3, a4, a5, a6, a7, a8] where
  injNP (a1, a2, a3, a4, a5, a6, a7, a8) = a1 :* a2 :* a3 :* a4 :* a5 :* a6 :* a7 :* a8 :* Nil

instance InjNP (f a1, f a2, f a3, f a4, f a5, f a6, f a7, f a8, f a9) f '[a1, a2, a3, a4, a5, a6, a7, a8, a9] where
  injNP (a1, a2, a3, a4, a5, a6, a7, a8, a9) = a1 :* a2 :* a3 :* a4 :* a5 :* a6 :* a7 :* a8 :* a9 :* Nil

instance InjNP (f a1, f a2, f a3, f a4, f a5, f a6, f a7, f a8, f a9, f a10) f '[a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] where
  injNP (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) = a1 :* a2 :* a3 :* a4 :* a5 :* a6 :* a7 :* a8 :* a9 :* a10 :* Nil
