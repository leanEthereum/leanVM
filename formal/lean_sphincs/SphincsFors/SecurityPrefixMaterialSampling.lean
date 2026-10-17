import SphincsFors.SecurityPrefixPrepared

/-! Replacing the low 128-bit secret of a selected candidate chain in the full prepared material,
keeping its high 128 bits and every other material entry, and material whose selected secret is
erased. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open SeedModel SphincsBase.Concrete.UniformTableSplit

attribute [local instance] Classical.propDecidable

noncomputable def replaceMaterial (segment : Segment) (material : Material) (value : Digest) : Material :=
  (material.1, Function.update material.2 (.inl (address segment))
    (combine value (splitHashOutput digestBits (material.2 (.inl (address segment)))).2))

abbrev ErasedMaterial (segment : Segment) :=
  {material : Material // truncateHash (material.2 (.inl (address segment))) = 0}

instance (segment : Segment) : Nonempty (ErasedMaterial segment) := ⟨⟨(0, fun _ => 0), rfl⟩⟩

end SphincsFors.Security.Prefix
