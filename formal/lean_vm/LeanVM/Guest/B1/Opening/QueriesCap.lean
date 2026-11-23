/-
  LeanVM.Guest.B1.Opening.QueriesCap

  One query's cap leaf: the parent's flag set and the node reached stored at the cap leaf.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPath

/-!
# A query's cap leaf (`walk_path`, inline)

The last two windows of the position are `wb = g^b`, `b` its bit `pd`, and `q = g^Q`,
`Q = pos / 2^(pd+1)` (the parent's index among the cap's internal nodes at the level above the
leaves); the parent's flag `flags[Q]` is set to `1`, and the node reached is stored at the cap
leaf `cap·q⁴·wb²`: the cells `2(pos / 2^pd)` and the next (`oqCap_sound`), the caller having
offset `cap` and `flags` past the levels above.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The path's windows at `pd` levels below the cap. -/
abbrev npwOf (pd : ℕ) : ℕ := (pd + 5) / 6

theorem oqNpw_eq (s : Oq) : oqNpw s = npwOf s.pd := rfl

/-- The cap child bit's window: `(q >>> pd) % 2`. -/
theorem qwVal_capBit {pd cd q : ℕ} :
    qwVal (pd + cd) cd q (npwOf pd) = (if q.testBit pd then 1 else 0) := by
  simp only [qwVal, qwWin, qwNp, npwOf, Nat.add_sub_cancel, ↓reduceIte, pow_one,
    Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ pd) with h | h <;> simp [h]

/-- The cap parent index's window: `q / 2^(pd+1)`. -/
theorem qwVal_capIdx {pd cd q : ℕ} (hcd : 1 ≤ cd) (hq : q < 2 ^ (pd + cd)) :
    qwVal (pd + cd) cd q (npwOf pd + 1) = q / 2 ^ (pd + 1) := by
  have h1 : (pd + 5) / 6 + 1 ≠ (pd + 5) / 6 := by omega
  simp only [qwVal, qwWin, qwNp, npwOf, Nat.add_sub_cancel, h1, ↓reduceIte,
    Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  calc q < 2 ^ (pd + cd) := hq
    _ = 2 ^ (cd - 1 + (pd + 1)) := by congr 1; omega

/-- **The cap leaf** (`walk_path`'s end): with the last two windows those of `q < 2^(pd+cd)`
(`wb = g^b`, `q' = g^(q / 2^(pd+1))`), the parent's flag is set and the node at `n, n + 1` is
stored at the cap leaf's cells. -/
theorem oqCap_sound {pd cd : ℕ} (hcd : 1 ≤ cd) {bp cap flags : V} {k n q : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqCapT bp cap flags k n (npwOf pd) → a.Holds rd σ)
    (hq : q < 2 ^ (pd + cd))
    (hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (pd + cd) cd →
      v = gen ^ qwVal (pd + cd) cd q i) :
    LoadHolds rd (σ flags) (q / 2 ^ (pd + 1)) 1 ∧
      LoadHolds rd (σ cap) (2 * (q / 2 ^ pd)) (σ (.n n)) ∧
      LoadHolds rd (σ cap) (2 * (q / 2 ^ pd) + 1) (σ (.n (n + 1))) := by
  have hN : npwOf pd + 1 < qwN (pd + cd) cd := by
    simp [qwN, qwNp, npwOf]
  have c0 := hA _ (by simp [oqCapT] : Stmt.atom (.load (.n k) bp (npwOf pd)) ∈ _)
  have c1 := hA _ (by simp [oqCapT] : Stmt.atom (.load (.n (k + 1)) bp (npwOf pd + 1)) ∈ _)
  have c2 := hA _ (by simp [oqCapT] : Stmt.atom (.mul (.n (k + 2)) flags (.n (k + 1))) ∈ _)
  have c3 := hA _ (by simp [oqCapT] : Stmt.atom (.const (.n (k + 3)) (word 1 0)) ∈ _)
  have c4 := hA _ (by simp [oqCapT] : Stmt.atom (.load (.n (k + 3)) (.n (k + 2)) 0) ∈ _)
  have c5 := hA _ (by simp [oqCapT] : Stmt.atom (.mul (.n (k + 4)) (.n (k + 1)) (.n (k + 1))) ∈ _)
  have c6 := hA _ (by simp [oqCapT] : Stmt.atom (.mul (.n (k + 5)) cap (.n (k + 4))) ∈ _)
  have c7 := hA _ (by simp [oqCapT] : Stmt.atom (.mul (.n (k + 6)) (.n (k + 5)) (.n (k + 4))) ∈ _)
  have c8 := hA _ (by simp [oqCapT] : Stmt.atom (.mul (.n (k + 7)) (.n k) (.n k)) ∈ _)
  have c9 := hA _ (by simp [oqCapT] : Stmt.atom (.mul (.n (k + 8)) (.n (k + 6)) (.n (k + 7))) ∈ _)
  have c10 := hA _ (by simp [oqCapT] : Stmt.atom (.load (.n n) (.n (k + 8)) 0) ∈ _)
  have c11 := hA _ (by simp [oqCapT] : Stmt.atom (.load (.n (n + 1)) (.n (k + 8)) 1) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
  set Q := q / 2 ^ (pd + 1) with hQdef
  set b : ℕ := if q.testBit pd then 1 else 0 with hbdef
  have hwb : σ (.n k) = gen ^ b := by
    rw [hwin _ _ c0 (by omega), qwVal_capBit]
  have hwq : σ (.n (k + 1)) = gen ^ Q := by
    rw [hwin _ _ c1 hN, qwVal_capIdx hcd hq]
  have hz8 : σ (.n (k + 8)) = σ cap * gen ^ (4 * Q + 2 * b) := by
    rw [c9, c7, c6, c5, c8, hwb, hwq, ← pow_add, ← pow_add, mul_assoc, ← pow_add, mul_assoc,
      ← pow_add]
    congr 2; ring
  have hsplit : q / 2 ^ pd = 2 * Q + b := by
    rw [hQdef, hbdef, Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    by_cases h : q / 2 ^ pd % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [c2, hwq, c3, word_one, loadHolds_mul_gen_pow, Nat.add_zero] at c4
    exact c4
  · rw [hz8, loadHolds_mul_gen_pow, Nat.add_zero] at c10
    rw [hsplit, show 2 * (2 * Q + b) = 4 * Q + 2 * b by ring]
    exact c10
  · rw [hz8, loadHolds_mul_gen_pow] at c11
    rw [hsplit, show 2 * (2 * Q + b) + 1 = 4 * Q + 2 * b + 1 by ring]
    exact c11

end
end LeanVM.Guest.B1
