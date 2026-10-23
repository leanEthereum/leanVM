/-
  LeanVMTests.Protocol.Whir.Fold

  Folds over `ZMod 5`: one coordinate, many coordinates against the eq-weighted sum and the
  iterated fold, and a challenge at which folding creates a new close codeword.
-/

import LeanVM.Protocol.ToArkLib.Whir.Fold
import Mathlib.Algebra.Field.ZMod

/-!
# Fold controls

* `fold` computes `(1 - s) O₀ + s O₁` row by row; `foldMany` agrees with the eq-weighted sum and
  with folding coordinate `0` first (`foldMany_succ`).
* **Negative control.** For the constant code (degree below `1`) on the points `0, 1` of
  `ZMod 5`, the word with rows `(0, 1)` and `(1, 0)` has an empty list at full agreement, but its
  fold at `s = 3` is the constant `(3, 3)`. So `3` is a bad challenge, the inclusion
  `Λ(fold s O) ⊆ fold s '' Λ(O)` is not automatic, and no exact line agreement bound with zero
  exceptional challenges holds: the count of `card_foldBad_le_of_lineExact` is load-bearing.
-/

namespace LeanVMTests.Protocol.Whir

open LeanVM.Protocol.Whir Polynomial CompPoly CMlPolynomialEval ReedSolomon.HiddenDerivative

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## One coordinate -/

private def pairWord : Bool × Unit → Fin 2 → ZMod 5 := fun r ↦ if r.1 then ![1, 0] else ![0, 1]

#guard fold (3 : ZMod 5) pairWord () = ![3, 3]
#guard fold (0 : ZMod 5) pairWord () = ![0, 1]
#guard fold (1 : ZMod 5) pairWord () = ![1, 0]
#guard decide (∀ s : ZMod 5, ∀ x, fold s pairWord () x =
  pairWord (false, ()) x + s * (pairWord (true, ()) x - pairWord (false, ()) x))

/-! ## Many coordinates -/

private def cubeWord : Fin (2 ^ 2) × Unit → Fin 1 → ZMod 5 := fun r _ ↦ ![1, 4, 2, 0] r.1
private def point : Vector (ZMod 5) 2 := #v[2, 3]

#guard foldMany point cubeWord () 0 =
  ∑ i : Fin (2 ^ 2), (lagrangeBasis point)[i] * cubeWord (i, ()) 0
#guard foldMany point cubeWord () 0 =
  foldMany point.tail (fold point.head (pairUp cubeWord)) () 0
-- The first coordinate is the low index bit: rows `0, 1` are paired, not rows `0, 2`.
#guard pairUp cubeWord (true, (0, ())) 0 = 4
#guard foldMany #v[(1 : ZMod 5), 0] cubeWord () 0 = 4

/-- The fold of encoded rows is the encoding of the folded messages, for any linear encoder. -/
example (enc : (Fin 2 → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5))
    (g : Fin (2 ^ 2) × Unit → Fin 2 → ZMod 5) :
    foldMany point (fun r ↦ enc (g r)) = fun u ↦ enc (foldMany point g u) :=
  foldMany_encoder enc point g

/-! ## The fold-list lemma -/

/-- The Johnson fold-list count, stated for lines on four points of `ZMod 5` at `η = 1/4`. -/
example (domain : Fin 4 ↪ ZMod 5) (O : Bool × Unit → Fin 4 → ZMod 5)
    (ha : johnsonAgreement 4 1 (1 / 4) ≤ 1) :
    (foldBad (ReedSolomon.code domain 2) ⌈johnsonAgreement 4 1 (1 / 4) * 4⌉₊ O).card ≤
      Fintype.card Unit * ⌊johnsonExceptionCount 4 1 ⌈johnsonAgreement 4 1 (1 / 4) * 4⌉₊
        (1 / 4)⌋₊ :=
  card_foldBad_le_johnson domain (by decide) (by decide) (by norm_num) ha O

/-- The points `0, 1` of `ZMod 5`. -/
private def dom2 : Fin 2 ↪ ZMod 5 := ⟨![0, 1], by decide⟩

/-- A word of the constant code (degree below `1`) is constant. -/
private theorem const_of_mem_code {u : Fin 2 → ZMod 5} (hu : u ∈ ReedSolomon.code dom2 1) :
    u 0 = u 1 := by
  obtain ⟨P, hP, hPu⟩ := ReedSolomon.mem_code_iff_eval.mp hu
  have hP0 : P = C (P.coeff 0) := eq_C_of_degree_le_zero (Order.le_of_lt_succ hP)
  rw [← hPu 0, ← hPu 1, hP0, eval_C, eval_C]

private theorem iList_pairWord_eq_empty :
    iList (ReedSolomon.code dom2 1) 2 pairWord = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun U hU ↦ ?_
  rw [mem_iList, isClose_iff_le_card_agreeSet] at hU
  have hall : agreeSet pairWord U = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) (by simpa using hU.2))
  have h0 := (mem_agreeSet pairWord U 0).mp (hall ▸ Finset.mem_univ _) (false, ())
  have h1 := (mem_agreeSet pairWord U 1).mp (hall ▸ Finset.mem_univ _) (false, ())
  have hc := const_of_mem_code (hU.1 (false, ()))
  rw [← h0, ← h1] at hc
  revert hc
  decide

/-- **Negative control.** Folding at `3` creates a close codeword with no preimage in the
list. -/
theorem three_mem_foldBad : (3 : ZMod 5) ∈ foldBad (ReedSolomon.code dom2 1) 2 pairWord := by
  rw [mem_foldBad, iList_pairWord_eq_empty, Finset.image_empty]
  refine Finset.ne_empty_of_mem (a := fun _ _ ↦ (3 : ZMod 5)) ?_
  rw [mem_iList, isClose_iff_le_card_agreeSet]
  refine ⟨fun _ ↦ ReedSolomon.mem_code_iff_eval.mpr ⟨C 3, ?_, fun _ ↦ eval_C⟩, by decide⟩
  exact (degree_C_le).trans_lt (by decide)

/-- **Negative control.** No exact line agreement bound with zero exceptional challenges holds
for the constant code on two points at full agreement. -/
example : ¬ ReedSolomon.LineExactAgreementBound dom2 1 2 0 := by
  intro h
  have := card_foldBad_le_of_lineExact dom2 h pairWord
  simp only [Nat.floor_zero, mul_zero, Nat.le_zero, Finset.card_eq_zero] at this
  exact Finset.notMem_empty _ (this ▸ three_mem_foldBad)

end LeanVMTests.Protocol.Whir
