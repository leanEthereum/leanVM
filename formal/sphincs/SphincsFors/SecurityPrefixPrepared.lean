import SphincsFors.SecurityPrefixCountedSign
import SphincsBase.Proof.Reference.QueryAllocation
import SphincsBase.Proof.Chains.AdaptiveChainCapCost
import SphincsFors.SecurityMaterialGameCoupling

/-! The chain secrets read from prepared material (`materialSecrets`). -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open Concrete SeedModel PreparedScheme SeedCoupling

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] programCache digestAttemptLimit encodingAttemptLimit
  Randomized.sign Randomized.finishSign

def materialSecrets (material : Material) : Secrets :=
  fun chain => truncateHash (material.2 (.inl chain))

end SphincsFors.Security.Prefix
