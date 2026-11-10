module

public import FORS.Scheme.Uniform

@[expose] public section

/-!
# Counting values by their low bits

A value of `HashOutput` has `2^128` values with the same low 128 bits
(`Qrom.Sphincs.card_trunc_fiber`), so among the functions from a finite type, those whose value at a
given point has given low bits are a fraction `2^-128` (`Qrom.Sphincs.card_trunc_at_le`).
-/

open FORS

noncomputable section

namespace Qrom.Sphincs

variable [Params]

theorem card_trunc_fiber (v : Digest) :
    (Finset.univ.filter fun z : HashOutput ↦ truncateHash z = v).card = 2 ^ 128 := by
  let e := Equiv.ofBijective (splitHashOutputAt 0 digestBits)
    (splitHashOutputAt_bijective (by decide))
  have h1 : (Finset.univ.filter fun z : HashOutput ↦ truncateHash z = v).card =
      Fintype.card {z : HashOutput // (e z).1 = v} := by
    rw [Fintype.card_subtype]
    rfl
  have h2 : Fintype.card {z : HashOutput // (e z).1 = v} =
      Fintype.card {p : BitVec digestBits × (BitVec 0 × BitVec (hashOutputBits - (0 + digestBits))) //
        p.1 = v} :=
    Fintype.card_congr (e.subtypeEquiv fun _ ↦ Iff.rfl)
  have h3 : Fintype.card {p : BitVec digestBits × (BitVec 0 × BitVec (hashOutputBits - (0 + digestBits))) //
      p.1 = v} = Fintype.card (BitVec 0 × BitVec (hashOutputBits - (0 + digestBits))) :=
    Fintype.card_congr
      { toFun := fun p ↦ p.1.2, invFun := fun q ↦ ⟨(v, q), rfl⟩,
        left_inv := fun ⟨⟨a, q⟩, ha⟩ ↦ by cases ha; rfl, right_inv := fun _ ↦ rfl }
  rw [h1, h2, h3, Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec]
  rfl

omit [Params] in
theorem card_hashOutput : Fintype.card HashOutput = 2 ^ 256 := by
  rw [Fintype.card_bitVec]
  rfl

/-- Among the functions to `HashOutput`, those with given low bits at `c` are a fraction `2^-128`. -/
theorem card_trunc_at_le {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι) (v : Digest)
    (P : (ι → HashOutput) → Prop) [DecidablePred P] (hP : ∀ b, P b → truncateHash (b c) = v) :
    ((Finset.univ.filter P).card : ℝ) ≤ (2 : ℝ)⁻¹ ^ 128 * Fintype.card (ι → HashOutput) := by
  have hsub : (Finset.univ.filter P).card ≤
      (Finset.univ.filter fun b : ι → HashOutput ↦ truncateHash (b c) = v).card :=
    Finset.card_le_card fun b hb ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact hP b hb
  let e := Equiv.piSplitAt c fun _ ↦ HashOutput
  have hcount : (Finset.univ.filter fun b : ι → HashOutput ↦ truncateHash (b c) = v).card =
      2 ^ 128 * Fintype.card ({j // j ≠ c} → HashOutput) := by
    rw [← card_trunc_fiber v, ← Fintype.card_coe, ← Fintype.card_coe, ← Fintype.card_prod]
    exact Fintype.card_congr
      { toFun := fun b ↦ (⟨(e b.1).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp b.2).2⟩⟩, (e b.1).2)
        invFun := fun q ↦ ⟨e.symm (q.1.1, q.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          have := (Finset.mem_filter.mp q.1.2).2
          simpa [e] using this⟩⟩
        left_inv := fun b ↦ by simp
        right_inv := fun q ↦ by simp }
  have htot : Fintype.card (ι → HashOutput) = 2 ^ 256 * Fintype.card ({j // j ≠ c} → HashOutput) := by
    rw [Fintype.card_congr e, Fintype.card_prod, card_hashOutput]
  have hle : ((Finset.univ.filter P).card : ℝ) ≤
      (2 : ℝ) ^ 128 * Fintype.card ({j // j ≠ c} → HashOutput) := by
    exact_mod_cast hsub.trans hcount.le
  refine hle.trans (le_of_eq ?_)
  rw [htot]
  push_cast
  ring

end Qrom.Sphincs
