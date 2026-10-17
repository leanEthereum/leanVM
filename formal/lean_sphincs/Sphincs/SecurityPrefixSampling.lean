import Sphincs.SecurityPrefixOracle
import SphincsBase.Proof.Base.UniformTableSplit

/-!
Chain addresses, secret tables indexed by them, the address of a selected prefix segment, and
secret tables whose selected coordinate is erased. Adapted from leanVM's OtsPrefixSecretSampling.
-/

open OracleComp OracleSpec

namespace Sphincs.Security.Prefix
open SphincsBase.Concrete.UniformTableSplit

attribute [local instance] Classical.propDecidable

abbrev ChainAddress := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev Secrets := ChainAddress → Digest

def address (segment : Segment) : ChainAddress :=
  (segment.lay, segment.tree, segment.leaf, segment.chainIdx)

abbrev ErasedSecrets (segment : Segment) := {secrets : Secrets // secrets (address segment) = 0}

instance (segment : Segment) : Nonempty (ErasedSecrets segment) := ⟨⟨fun _ => 0, rfl⟩⟩

end Sphincs.Security.Prefix
