/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/

/-
  LeanVM.Protocol.ToCompPoly.AmbientStacking

  The multilinear extension of an aligned stack at an arbitrary point, for any pad. Candidate
  for CompPoly.
-/

module

public import LeanVM.Protocol.ToCompPoly.Stacking

/-!
# A stack at an arbitrary point

At a point whose high coordinates are not selector bits, every block contributes. The block
`b` contributes its extension at the point's low coordinates, weighted by
`selectorWeight b`, the Lagrange basis of the high coordinates at the block's selector; the
cells no block covers contribute the pad, weighted by what is left of the partition of unity
(`stack_eval_ambient`). When the blocks fill the stack the weights sum to one
(`sum_selectorWeight_of_total_eq`).
`stack_eval₂_ambient` is the statement at a point of another ring than the entries. Over an
arbitrary commutative ring.

Candidate for CompPoly, beside `CompPoly.Multilinear`. The request it answers is tracked
upstream as [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900). Nothing here
transcribes a source.

Derived from Verified-zkEVM/leanth at 23929f8c922cd4461ab22dbfaa6520f3ad23a3b2,
`Leanth/LeanVM/Protocol.lean:9818-9850` (`eval_MLE_stack_ambient`), by Aristotle (Harmonic),
Stefano Rocca and Elias Judin. The source statement, for pad zero, is extended to any pad and
to a point of another ring.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

private theorem evalMle_map_sub_const {n : ℕ} (t : CMlPolynomialEval R n) (a : R)
    (z : Vector R n) :
    evalMle (Vector.map (fun x ↦ x - a) t) z = evalMle t z - a := by
  rw [evalMle_eq_sum]
  simp only [Fin.getElem_fin, Vector.getElem_map, sub_mul, Finset.sum_sub_distrib]
  have hc : (∑ i : Fin (2 ^ n), a * (lagrangeBasis z)[i.val]) = a := by
    simpa only [evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_replicate] using
      evalMle_replicate a z
  rw [hc]
  congr 1
  exact (evalMle_eq_sum t z).symm

namespace Blocks

variable (B : Blocks)

/-- The weight of block `b` at a point of the stack: the Lagrange basis of the point's high
coordinates at the block's selector. -/
def selectorWeight {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R μ) : R :=
  (lagrangeBasis (B.highPoint hμ b z))[B.selector hμ b]

/-- A table placed in a block's window, zero outside it. -/
def windowTable {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (t : CMlPolynomialEval R (B.size b)) : CMlPolynomialEval R μ :=
  Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel' (B.size_le hμ b)))
    (placeSlice t (B.selector hμ b))

/-- A window table reads the local value inside its window and vanishes outside it. -/
theorem windowTable_getElem {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (t : CMlPolynomialEval R (B.size b)) (x : Fin (2 ^ μ)) :
    (B.windowTable hμ b t)[x] = if h : B.InWindow b x.val then
      t[x.val - B.offset b]'(by have := h.2; omega) else 0 := by
  simp only [windowTable, Fin.getElem_fin, Vector.getElem_cast, placeSlice,
    Vector.getElem_ofFn, selector_val]
  by_cases hx : B.InWindow b x.val
  · have hd := (B.inWindow_iff_div b x.val).mp hx
    have hm := Nat.mod_add_div x.val (2 ^ B.size b)
    rw [hd, Nat.mul_div_cancel' (B.pow_size_dvd_offset b)] at hm
    have he : x.val % 2 ^ B.size b = x.val - B.offset b := by omega
    simp [hx, hd, he]
  · simp [hx, (B.inWindow_iff_div b x.val).not.mp hx]

/-- The extension of a window table is the table's extension at the low coordinates, times the
block's weight. -/
theorem evalMle_windowTable {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (t : CMlPolynomialEval R (B.size b)) (z : Vector R μ) :
    evalMle (B.windowTable hμ b t) z =
      B.selectorWeight hμ b z * evalMle t (B.lowPoint hμ b z) := by
  conv_lhs => rw [← B.cast_lowPoint_append_highPoint hμ b z]
  rw [windowTable, evalMle_cast, evalMle_placeSlice]
  rfl

/-- The stack is the constant pad plus, on each window, the block minus the pad. -/
theorem stackAt_decomposition (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R) :
    B.stackAt t μ pad = Vector.ofFn (fun x ↦ pad +
      ∑ b : Fin B.n, (B.windowTable hμ b (Vector.map (fun v ↦ v - pad) (t b)))[x]) := by
  apply Vector.ext
  intro x hx
  simp only [Vector.getElem_ofFn]
  by_cases hp : B.total ≤ x
  · rw [B.stackAt_getElem_of_total_le t pad hx hp]
    have hn : ∀ b : Fin B.n, ¬ B.InWindow b x := by
      intro b hb
      have := B.offset_add_pow_le_total b
      omega
    simp [B.windowTable_getElem, hn]
  · obtain ⟨b, hb⟩ := B.exists_inWindow (Nat.lt_of_not_ge hp)
    rw [B.stackAt_getElem_of_inWindow t (b := b) pad hx hb, Finset.sum_eq_single b]
    · rw [B.windowTable_getElem, dite_eq_left hb]
      simp
    · intro c _ hc
      rw [B.windowTable_getElem, dite_eq_right (fun hh ↦ hc (B.inWindow_unique hh hb))]
    · simp

/-- The stack at an arbitrary point: every block at the point's low coordinates, weighted by
its selector at the high ones, plus the pad times the weight no block covers. -/
theorem stack_eval_ambient (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R)
    (z : Vector R μ) :
    evalMle (B.stackAt t μ pad) z =
      (∑ b : Fin B.n, B.selectorWeight hμ b z * evalMle (t b) (B.lowPoint hμ b z)) +
        pad * (1 - ∑ b : Fin B.n, B.selectorWeight hμ b z) := by
  rw [B.stackAt_decomposition t hμ pad, evalMle_eq_sum]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hc : (∑ i : Fin (2 ^ μ), pad * (lagrangeBasis z)[i.val]) = pad := by
    simpa only [evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_replicate] using
      evalMle_replicate pad z
  rw [hc]
  have ht (b : Fin B.n) :
      (∑ i : Fin (2 ^ μ), (B.windowTable hμ b (Vector.map (fun v ↦ v - pad) (t b)))[i.val] *
        (lagrangeBasis z)[i.val]) =
        B.selectorWeight hμ b z * (evalMle (t b) (B.lowPoint hμ b z) - pad) := by
    simpa only [evalMle_eq_sum, Fin.getElem_fin] using
      (B.evalMle_windowTable hμ b (Vector.map (fun v ↦ v - pad) (t b)) z).trans
        (congrArg (B.selectorWeight hμ b z * ·)
          (evalMle_map_sub_const (t b) pad (B.lowPoint hμ b z)))
  simp_rw [ht, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

/-- When the blocks fill the stack, their weights sum to one at every point. -/
theorem sum_selectorWeight_of_total_eq {μ : ℕ} (h : B.total = 2 ^ μ) (z : Vector R μ) :
    (∑ b : Fin B.n, B.selectorWeight h.le b z) = 1 := by
  let t : B.Tables R := fun b ↦ Vector.replicate (2 ^ B.size b) 0
  have h0 := B.stack_eval_ambient t h.le 0 z
  have h1 := B.stack_eval_ambient t h.le 1 z
  rw [B.stackAt_eq_of_total_eq t h 1 0, h0] at h1
  have hc : (0 : R) = 1 * (1 - ∑ b : Fin B.n, B.selectorWeight h.le b z) :=
    add_left_cancel (by simpa only [zero_mul, add_zero] using h1)
  rw [one_mul] at hc
  exact (sub_eq_zero.mp hc.symm).symm

end Blocks

end
end LeanVM.Protocol
