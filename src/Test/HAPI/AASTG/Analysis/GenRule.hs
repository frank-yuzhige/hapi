module Test.HAPI.AASTG.Analysis.GenRule where
import Test.HAPI.AASTG.Analysis.ProcType (ProcType, UnboundedProcTypeMap, isSubType')
import Test.HAPI.AASTG.Core (AASTG)
import Test.HAPI.Effect.Eff (Alg)
import Test.HAPI.AASTG.Analysis.Rename (VarSubstitution)

data GenRule api c = GenRule { grGiven :: ProcType, grDerive :: AASTG api c }
  deriving Eq

ruleApplicable :: Alg sig m => GenRule api c -> ProcType -> m (Maybe VarSubstitution)
ruleApplicable (GenRule t _) = return . isSubType' t

unsafeApplyRule :: GenRule api c -> AASTG api c -> AASTG api c
unsafeApplyRule (GenRule _ a) aastg = _
