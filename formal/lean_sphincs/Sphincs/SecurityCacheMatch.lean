import Sphincs.Statement
import Sphincs.RandomizedSupport
import Sphincs.SecurityTreeWitness
import Sphincs.Uniform

/-!
Cached matches against fixed input-indexed target sets: a cache is bad when some cached answer
truncates into the target set of its input. Canonical inputs can be excluded by assigning them the
empty target set.
-/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.CacheMatch

open Completeness

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def Bad (targets : HashInput → Finset Digest) (cache : QueryCache HashSpec) : Prop :=
  ∃ input answer, cache input = some answer ∧ truncateHash answer ∈ targets input

end Sphincs.Security.CacheMatch
