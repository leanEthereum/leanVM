module

public import XmssSecurity.Proof.HiddenValue
public import XmssSecurity.Proof.EvalDistEq
public import VCVio.OracleComp.Constructions.SampleableType

@[expose] public section

open OracleComp ENNReal

namespace XmssSecurity.IndexedHiddenValue

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable local instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

noncomputable local instance : SampleableType (Index → Digest) :=
  SampleableType.ofFintype (Index → Digest)

theorem uniform_table_coordinate_probability (index : Index) (target : Digest) :
    Pr{let table ← $ᵗ (Index → Digest)}[table index = target] =
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
      (evaluate <$> ((fun table : Index → Digest => table ∘ embed) <$> ($ᵗ (Index → Digest)))) =ᵈ ($ᵗ Digest) := by
    have hrestrict :
        ((fun table : Index → Digest => table ∘ embed) <$> ($ᵗ (Index → Digest))) =ᵈ
          ($ᵗ (Unit → Digest)) :=
      evalDistEq_uniformSample_map_comp_injective (R := Digest) hembed
    exact (hrestrict.map evaluate).trans
      (SampleableType.map_uniformSample_evalDistEq_of_bijective hevaluate)
  calc
    Pr{let table ← $ᵗ (Index → Digest)}[table index = target] =
        Pr{let value ← evaluate <$> ((fun table : Index → Digest => table ∘ embed) <$> ($ᵗ (Index → Digest)))}[value = target] := by
      rw [prEvent_map, prEvent_map]
      rfl
    _ = Pr{let value ← $ᵗ Digest}[value = target] :=
      hmarginal.prEvent_eq (· = target)
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [SampleableType.prEvent_uniformSample_eq_singleton, HiddenValue.card_digest]


end XmssSecurity.IndexedHiddenValue
