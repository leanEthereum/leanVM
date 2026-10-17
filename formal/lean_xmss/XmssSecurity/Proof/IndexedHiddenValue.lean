import XmssSecurity.Proof.HiddenValue
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp ENNReal

namespace XmssSecurity.IndexedHiddenValue

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable local instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

noncomputable local instance : SampleableType (Index → Digest) :=
  SampleableType.ofFintype (Index → Digest)

theorem uniform_table_coordinate_probability (index : Index) (target : Digest) :
    Pr[fun table : Index → Digest => table index = target | $ᵗ (Index → Digest)] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let embed : Unit → Index := fun _ => index
  have hembed : Function.Injective embed := by
    intro left right _
    cases left
    cases right
    rfl
  let evaluate : (Unit → Digest) → Digest := fun table => table ()
  have hevaluate : Function.Bijective evaluate := by
    constructor
    · intro left right heq
      funext input
      cases input
      exact heq
    · intro value
      exact ⟨fun _ => value, rfl⟩
  have hmarginal :
      𝒟[evaluate <$> ((fun table : Index → Digest => table ∘ embed) <$> ($ᵗ (Index → Digest)))] =
        𝒟[$ᵗ Digest] := by
    have hrestrict :
        𝒟[(fun table : Index → Digest => table ∘ embed) <$> ($ᵗ (Index → Digest))] =
          𝒟[$ᵗ (Unit → Digest)] := by
      simpa [bind_pure_comp] using
        evalDist_uniformSample_map_comp_injective (R := Digest) hembed
    rw [evalDist_map, hrestrict, ← evalDist_map]
    exact evalDist_map_bijective_uniform_cross
      (α := Unit → Digest) (β := Digest) evaluate hevaluate
  calc
    Pr[fun table : Index → Digest => table index = target | $ᵗ (Index → Digest)] =
        Pr[fun value : Digest => value = target |
          evaluate <$> ((fun table : Index → Digest => table ∘ embed) <$> ($ᵗ (Index → Digest)))] := by
      rw [probEvent_map, probEvent_map]
      rfl
    _ = Pr[fun value : Digest => value = target | $ᵗ Digest] :=
      probEvent_congr' (fun _ _ => Iff.rfl) hmarginal
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      by simpa only [probEvent_eq_eq_probOutput] using
        HiddenValue.uniform_digest_point_probability target

end XmssSecurity.IndexedHiddenValue
