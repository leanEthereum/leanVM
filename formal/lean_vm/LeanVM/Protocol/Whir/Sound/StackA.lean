/-
  LeanVM.Protocol.Whir.Sound.StackA

  Level 0's stack from the array of its tuple's values.
-/

module

public import LeanVM.Protocol.Whir.Sound.DescentT
public import LeanVM.Protocol.EndToEnd.Sound.ExtractorC

/-!
# Level 0's stack over arrays

`stackA μ VA`: cell `i` of the stack is entry `i mod 2^κ` of the inverse transform of the first
limb of lane `i / 2^κ`'s values on the first `2^κ` columns, `κ = μ − 6`; it is `stackV` on the
tuple the array holds (`stackA_eq`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Sound

@[expose] public section

/-- **Level 0's stack from its tuple's array.** -/
def stackA (μ : ℕ) (VA : AV) : Vector K (2 ^ μ) :=
  let κ := μ - laneBits
  let lows := Array.ofFn fun u : Fin (2 ^ laneBits) ↦ Extraction.novelInv κ
    (limbArr 0 (Array.ofFn fun v : Fin (2 ^ κ) ↦ (VA.getD v #[]).getD u 0))
  Vector.ofFn fun i : Fin (2 ^ μ) ↦ (lows.getD (i / 2 ^ κ) #[]).getD (i % 2 ^ κ) 0

theorem novelInvE_limb0 (κ : ℕ) (y : Array E) {j : ℕ} (hj : j < 2 ^ κ) :
    ((novelInvE κ y).getD j 0).limb 0 = (Extraction.novelInv κ (limbArr 0 y)).getD j 0 := by
  simp only [novelInvE]
  rw [Prover.Enc.getD_ofFn _ _ _ hj, limb_ofLimbs, Matrix.cons_val_zero]

theorem stackA_eq {μ : ℕ} (hμ : laneBits ≤ μ) {n : ℕ} (hn : 2 ^ (μ - laneBits) ≤ n)
    (V : (Fin laneBits → Bool) → Fin n → E) :
    stackA μ (toAV n laneBits V) = (stackV hμ hn V).values := by
  have hκ : 0 < 2 ^ (μ - laneBits) := Nat.two_pow_pos _
  apply Vector.ext
  intro i hi
  have hu : i / 2 ^ (μ - laneBits) < 2 ^ laneBits := by
    rw [Nat.div_lt_iff_lt_mul hκ, ← pow_add, Nat.add_sub_cancel' hμ]; exact hi
  have hx : i % 2 ^ (μ - laneBits) < 2 ^ (μ - laneBits) := Nat.mod_lt _ hκ
  have hl : (stackA μ (toAV n laneBits V))[i] = (Extraction.novelInv (μ - laneBits) (limbArr 0
      (Array.ofFn fun v : Fin (2 ^ (μ - laneBits)) ↦
        ((toAV n laneBits V).getD v #[]).getD (i / 2 ^ (μ - laneBits)) 0))).getD
        (i % 2 ^ (μ - laneBits)) 0 := by
    simp only [stackA, Vector.getElem_ofFn]
    rw [Prover.Enc.getD_ofFn _ _ _ hu]
  have hr : (stackV hμ hn V).values[i] = ((novelInvE (μ - laneBits)
      (Array.ofFn fun v : Fin (2 ^ (μ - laneBits)) ↦ V ((bitsEquiv laneBits).symm
        ⟨i / 2 ^ (μ - laneBits), hu⟩) (Fin.castLE hn v))).getD (i % 2 ^ (μ - laneBits)) 0).limb 0 := by
    simp only [stackV, stackOf, Vector.getElem_ofFn, bitsToNat_symm]
  have harr : (Array.ofFn fun v : Fin (2 ^ (μ - laneBits)) ↦
      ((toAV n laneBits V).getD v #[]).getD (i / 2 ^ (μ - laneBits)) 0) =
      Array.ofFn fun v : Fin (2 ^ (μ - laneBits)) ↦ V ((bitsEquiv laneBits).symm
        ⟨i / 2 ^ (μ - laneBits), hu⟩) (Fin.castLE hn v) := by
    congr 1
    funext v
    have := rep_toAV V ((bitsEquiv laneBits).symm ⟨i / 2 ^ (μ - laneBits), hu⟩) (Fin.castLE hn v)
    rw [bitsToNat_symm] at this
    rw [this]
    rfl
  rw [hl, hr, harr, novelInvE_limb0 _ _ hx]

end
end LeanVM.Protocol.Whir.Sound
