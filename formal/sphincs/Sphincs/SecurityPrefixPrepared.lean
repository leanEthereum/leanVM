import Sphincs.SecurityPrefixCountedSign
import SphincsBase.Proof.Reference.QueryAllocation
import SphincsBase.Proof.Chains.AdaptiveChainCapCost
import Sphincs.SecurityMaterialGameCoupling

/-! The chain secrets read from prepared material (`materialSecrets`). -/

open OracleComp OracleSpec

namespace Sphincs.Security.Prefix
open Concrete SeedModel PreparedScheme SeedCoupling

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] programCache digestAttemptLimit encodingAttemptLimit
  Randomized.sign Randomized.finishSign

def materialSecrets (material : Material) : Secrets :=
  fun chain => truncateHash (material.2 (.inl chain))

end Sphincs.Security.Prefix
