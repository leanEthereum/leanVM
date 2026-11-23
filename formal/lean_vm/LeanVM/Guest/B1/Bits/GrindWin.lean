/-
  LeanVM.Guest.B1.Bits.GrindWin

  `grind_check` inlined is exact at every valuation holding its honest values on its own values.
-/

module

public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.Exact.Defs

/-!
# `grind_check` inlined, exact at its honest values

`gcInline_exact_of_vals`: on a valuation that is the honest one (`gcVals`) on the expansion's own values, every atom of
`gcInlineT b o w tabs` is exact on every memory: its two hints write the base-`2^11` windows of the word's low limb
above bit `b`, the executor's windows (`windowsExp`), and every other atom is no hint.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **A window of a word within its low limb** is the low limb's. -/
theorem wordNat_window (w : E) {s n : ℕ} (h : s + n ≤ 64) :
    (LeanVM.Prover.Exec.wordNat w >>> s) % 2 ^ n = kToNat (w.limb 0) / 2 ^ s % 2 ^ n := by
  have e : LeanVM.Prover.Exec.wordNat w = kToNat (w.limb 0) + 2 ^ s * (2 ^ n * (2 ^ (64 - s - n) *
      kToNat (w.limb 1))) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add,
      show s + n + (64 - s - n) = 64 by omega]
    rfl
  rw [e, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

/-- **`grind_check` inlined is exact at its honest values**: on a valuation holding `gcVals` on the expansion's own
values, every statement of it is an atom exact on every memory. -/
theorem gcInline_exact_of_vals {rd0 : Reader} {σ : Val} {b o : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hv : ∀ k, 2 ≤ k → k < gcLen b → σ (.n (o + k - 2)) = gcVals rd0 b (σ w) (σ tabs) k) :
    ∀ s ∈ gcInlineT b o w tabs, ∃ a, s = .atom a ∧ ∀ rd, a.Exact rd σ := by
  obtain ⟨hT1, hT, hsum⟩ := gc_shape b hb
  have hR : ∀ k, 2 ≤ k → k < gcLen b → σ (gcRen o w tabs (.n k)) = gcVals rd0 b (σ w) (σ tabs) k :=
    fun k h2 hk ↦ by rw [gcRen_own o w tabs h2]; exact hv k h2 hk
  intro s hs
  rw [gcInlineT] at hs
  obtain ⟨s0, hs0, e0⟩ := renameList_mem_inv hs
  simp only [gcPre, gcHead, gcTailPre, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_range] at hs0
  rcases hs0 with (hs0 | ⟨l, ⟨i, hi, rfl⟩, hs0⟩) | hs0
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Stmt.rename] at e0 <;> subst e0 <;>
      refine ⟨_, rfl, fun rd ↦ ?_⟩
    · show (((List.range (gcW b)).map fun j => V.n (2 + j)).map (gcRen o w tabs)).map σ =
        (List.range (gcW b)).map fun i ↦
          ofK (g ^ ((LeanVM.Prover.Exec.wordNat (σ (gcRen o w tabs (.n 0))) >>> (b + i * 11)) % 2 ^ 11))
      rw [gcRen_word, List.map_map, List.map_map]
      refine List.map_congr_left fun j hj ↦ ?_
      have hj : j < gcW b := List.mem_range.mp hj
      show σ (gcRen o w tabs (.n (2 + j))) = _
      rw [hR (2 + j) (by omega) (by unfold gcLen; omega), show 2 + j = gcW b + 2 - (gcW b - j) by omega,
        gv_win (by omega) (by omega), wordNat_window _ (by omega), gen_pow_eq_ofK, gcV,
        show gcW b - (gcW b - j) = j by omega, Nat.mul_comm 11 j]
    · show [σ (gcRen o w tabs (.n (gcW b + 2)))] = (List.range 1).map fun i ↦ ofK (g ^ ((LeanVM.Prover.Exec.wordNat
        (σ (gcRen o w tabs (.n 0))) >>> (b + 11 * gcW b + i * gcTop b)) % 2 ^ gcTop b))
      have hlt : kToNat ((σ w).limb 0) / 2 ^ (b + 11 * gcW b) < 2 ^ gcTop b := gcV_zero_lt hsum (σ w)
      simp only [List.range_one, List.map_cons, List.map_nil, Nat.zero_mul, Nat.add_zero]
      rw [hR (gcW b + 2) (by omega) (by unfold gcLen; omega), gv_top, gcRen_word, wordNat_window _ (by omega),
        Nat.mod_eq_of_lt hlt, gen_pow_eq_ofK, gcV, Nat.sub_zero]
    all_goals trivial
  · simp only [gcIterAt, List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Stmt.rename] at e0 <;> subst e0 <;>
      exact ⟨_, rfl, fun _ ↦ trivial⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Stmt.rename] at e0 <;> subst e0 <;>
      exact ⟨_, rfl, fun _ ↦ trivial⟩

end
end LeanVM.Guest.B1
