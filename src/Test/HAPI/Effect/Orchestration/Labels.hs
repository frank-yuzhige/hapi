{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.HAPI.Effect.Orchestration.Labels where
import Test.HAPI.Util.ByteSupplier (BiDir (..))


class LabelConsumeDir l d | l -> d where
  labelConsumeDir :: d

data QVSSupply
data EntropySupply

instance LabelConsumeDir QVSSupply BiDir where
  labelConsumeDir = BW

instance LabelConsumeDir EntropySupply BiDir where
  labelConsumeDir = FW
