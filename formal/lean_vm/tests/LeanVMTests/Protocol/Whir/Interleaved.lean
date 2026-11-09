/-
  LeanVMTests.Protocol.Whir.Interleaved

  Concrete interleaved Reed-Solomon words over `ZMod 5`, a list member, and the uniqueness
  threshold.
-/

import LeanVM.Protocol.ToArkLib.Whir.Interleaved
import Mathlib.Algebra.Field.ZMod

/-!
# Interleaved words and lists

A two-row word on three points of `ZMod 5`, against the code of polynomials of degree below `2`
(lines). The interleaved codeword with rows `X + 1` and `0` agrees with it on the two first
coordinates, so it is in the list at threshold `2` and not at threshold `3`.

Negative control for the uniqueness threshold: the lines `X` and `2X` are distinct codewords
agreeing at one point, so `eq_of_mem_code_of_agreeOn` fails with `k - 1 = 1` agreements in
place of `k = 2`.
-/

namespace LeanVMTests.Protocol.Whir

open LeanVM.Protocol.Whir Polynomial

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Three evaluation points `0, 1, 2` of `ZMod 5`. -/
private def dom3 : Fin 3 ↪ ZMod 5 := ⟨![0, 1, 2], by decide⟩

private def word : Fin 2 → Fin 3 → ZMod 5 := ![![1, 2, 3], ![0, 0, 4]]
private def cw : Fin 2 → Fin 3 → ZMod 5 := ![![1, 2, 3], ![0, 0, 0]]

#guard (agreeSet word cw).card = 2
#guard decide (∀ x, x ∈ agreeSet word cw ↔ x.val < 2)

private theorem cw_isInterleavedCodeword :
    IsInterleavedCodeword (ReedSolomon.code dom3 2) cw := by
  intro r
  fin_cases r
  · refine ReedSolomon.mem_code_iff_eval.mpr ⟨X + C 1, ?_, fun x ↦ ?_⟩
    · rw [degree_X_add_C]; decide
    · fin_cases x <;> simp [dom3, cw] <;> decide
  · have h0 : cw 1 = 0 := by funext x; fin_cases x <;> rfl
    exact h0 ▸ (ReedSolomon.code dom3 2).zero_mem

/-- The codeword is in the list at threshold `2`. -/
example : cw ∈ iList (ReedSolomon.code dom3 2) 2 word := by
  rw [mem_iList, isClose_iff_le_card_agreeSet]
  exact ⟨cw_isInterleavedCodeword, by decide⟩

/-- It is not in the list at threshold `3`: the words differ at the last coordinate. -/
example : cw ∉ iList (ReedSolomon.code dom3 2) 3 word := by
  rw [mem_iList, isClose_iff_le_card_agreeSet]
  exact fun h ↦ absurd h.2 (by decide)

/-- The relative-radius list at `γ = 1/3` asks for `2` agreements out of `3`. -/
example : radiusThreshold 3 (1 / 3) = 2 := by
  rw [radiusThreshold, show (1 - (1 / 3 : ℝ)) * (3 : ℕ) = 2 by norm_num]
  exact Nat.ceil_natCast 2

/-- Uniqueness of lines on two points, and its interleaved form. -/
example (U V : Fin 2 → Fin 3 → ZMod 5) (hU : IsInterleavedCodeword (ReedSolomon.code dom3 2) U)
    (hV : IsInterleavedCodeword (ReedSolomon.code dom3 2) V)
    (h : AgreeOn U V {0, 1}) : U = V :=
  eq_of_isInterleavedCodeword_of_agreeOn dom3 hU hV _ (by decide) h

/-- **Negative control.** One agreement does not determine a line. -/
example : ¬ ∀ u ∈ ReedSolomon.code dom3 2, ∀ v ∈ ReedSolomon.code dom3 2,
    ∀ S : Finset (Fin 3), 1 ≤ S.card → (∀ x ∈ S, u x = v x) → u = v := by
  intro h
  have hX : (fun x ↦ dom3 x) ∈ ReedSolomon.code dom3 2 :=
    ReedSolomon.mem_code_iff_eval.mpr ⟨X, by rw [degree_X]; decide, fun x ↦ by simp⟩
  have h2X : (fun x ↦ 2 * dom3 x) ∈ ReedSolomon.code dom3 2 :=
    ReedSolomon.mem_code_iff_eval.mpr ⟨C 2 * X, by
      rw [degree_C_mul_X (by decide)]; decide, fun x ↦ by simp⟩
  have := congrFun (h _ hX _ h2X {0} (by decide) (by simp [dom3])) 1
  revert this
  decide

end LeanVMTests.Protocol.Whir
