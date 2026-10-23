/-
  LeanVM.Protocol.ToVCVio.UniformSample

  The probability of an event with at most one witness under a uniform sample.
  Candidate for VCVio.
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The subsingleton bound for uniform samples

VCVio's `SampleableType.prEvent_uniformSample_le_div_iff` says that the probability of an
event under a uniform sample of a finite type is at most `c / |α|` exactly when the event has
at most `c` witnesses. The bound here is the form a soundness argument uses: an event any two
of whose witnesses are equal has probability at most `1/|α|`. It takes its hypothesis as a
statement about witnesses, so that no caller has to name the finite set of all elements of
the type, and its right-hand side is a non-negative real coerced to an extended one, the type
of a round-by-round error.
-/

namespace LeanVM.Protocol

open OracleComp
open scoped NNReal ENNReal

public section

variable {α : Type} [SampleableType α] [Fintype α]

/-- An event any two of whose witnesses are equal has probability at most `1/|α|` under a
uniform sample. -/
theorem prEvent_uniformSample_le_of_subsingleton (p : α → Prop)
    (h : ∀ a b, p a → p b → a = b) :
    Pr{let sample ← $ᵗ α}[p sample] ≤ ((1 / Fintype.card α : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hcard : (Finset.univ.filter p).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb ↦
      h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have := (SampleableType.prEvent_uniformSample_le_div_iff (p := p) (c := 1)).mpr hcard
  rwa [ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_one,
    ENNReal.coe_natCast, ← Nat.cast_one (R := ℝ≥0∞)]

end
end LeanVM.Protocol
