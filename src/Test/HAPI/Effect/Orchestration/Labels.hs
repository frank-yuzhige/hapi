{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.Effect.Orchestration.Labels where
import Test.HAPI.Util.ByteSupplier (BiDir (..))


class LabelConsumeDir l d | l -> d where
  labelConsumeDir :: d

data EVSSupply
data EntropySupply

instance LabelConsumeDir EVSSupply BiDir where
  labelConsumeDir = FW

instance LabelConsumeDir EntropySupply BiDir where
  labelConsumeDir = BW
