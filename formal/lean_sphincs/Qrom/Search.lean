module

public import Qrom.EventBound
public import Qrom.Bridge
public import Qrom.Cell
public import Qrom.PiKron
public import QuantumFoundations.MatrixMap.Norm

@[expose] public section

/-!
# Quantum search with a classical output

Let `good : X → Y → Prop` mark, for every input `z`, at most `s` of the `N = |Y|` values, and let
`λ = s / N`. A program that makes at most `t` calls to the quantum random oracle `H : X → Y` and
outputs, at each leaf `p`, a set `out p` of at most `k` inputs, outputs an input `z` with
`good z (H z)` with probability at most `λ (√6 t + 2 k)²` times the trace of its input
(`Qrom.qrom_search_le`).

## Proof

1. The check `∃ z ∈ out p, good z (H z)` on the hidden function is, on the compressed database,
   the operator `F diag(d) F` with `F` the compression of every cell and `d` the indicator of the
   total tables passing the check (`Qrom.sum_mul_trace_jointPost_additive_eq`). It is at most
   `F E F`, with `E` the projector onto the databases holding a good value at a cell of `out p`.
2. `F E F` is within `k · 2√λ` of `E` (`Qrom.norm_compress_orProj_sub_le`), from the one-cell
   bound `‖c G c - G‖ ≤ 2√λ` and the telescoping bound for operators acting cell by cell.
3. `E` lies below the event `Bad`: some cell holds a good value. A fresh cell enters `Bad` with
   probability at most `λ`, so the instability of `Bad` is at most `λ`
   (`Qrom.instability_searchEvent_le`), and a `t`-query program leaves weight at most `6 λ t²`
   on it (`Qrom.tsum_eventWeight_compressedRuntime_le`).
4. Per leaf, `√(check) ≤ √(Bad) + 2 k √λ √(trace)`, and the ℓ² Minkowski inequality sums the
   leaves.

The output is checked against `H` without being queried; checking `k` points costs as much as
`k` further queries would, which the term `2 k` accounts for.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ## The search event and its instability -/

section event

variable (good : X → Y → Prop) [∀ z, DecidablePred (good z)]

/-- The database holds a good value at some cell. -/
def searchEvent (D : Database X Y) : Bool :=
  decide (∃ z y, D z = some y ∧ good z y)

theorem searchEvent_empty : searchEvent good Database.empty = false := by
  simp [searchEvent, Database.empty]

/-- Filling a cell of a database outside the event enters it only with a good value. -/
theorem good_of_searchEvent_update {D : Database X Y} (hD : searchEvent good D = false) {x : X}
    {u : Y} (h : searchEvent good (Function.update D x (some u)) = true) : good x u := by
  simp only [searchEvent, decide_eq_true_eq, decide_eq_false_iff_not, not_exists, not_and] at h hD
  obtain ⟨z, y, hz, hg⟩ := h
  by_cases hzx : z = x
  · subst hzx
    rw [Function.update_self, Option.some.injEq] at hz
    exact hz ▸ hg
  · rw [Function.update_of_ne hzx] at hz
    exact absurd hg (hD z y hz)

/-- Filling a cell keeps a database in the event. -/
theorem searchEvent_update_of_true {D : Database X Y} (hD : searchEvent good D = true) {x : X}
    (hx : D x = none) (u : Y) : searchEvent good (Function.update D x (some u)) = true := by
  simp only [searchEvent, decide_eq_true_eq] at hD ⊢
  obtain ⟨z, y, hz, hg⟩ := hD
  refine ⟨z, y, ?_, hg⟩
  have hzx : z ≠ x := by
    rintro rfl
    rw [hx] at hz
    cases hz
  rw [Function.update_of_ne hzx, hz]

/-- **The instability of the search event** is at most the density of good values. -/
theorem instability_searchEvent_le [UniformAnswerMeasure (X →ₒ Y)] (s : ℕ)
    (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s) (t : ℕ) :
    Database.instability (searchEvent good) t ≤ (s : ℝ≥0∞) / Fintype.card Y := by
  rw [Database.instability_eq_iSup]
  refine iSup_le fun i ↦ iSup_le fun D ↦ iSup_le fun hD ↦ iSup_le fun _ ↦ iSup_le fun x ↦
    iSup_le fun hx ↦ ?_
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  refine (Finset.card_le_card fun u hu ↦ ?_).trans (hs x)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  cases i with
  | false => exact good_of_searchEvent_update good hD (Bool.not_eq_false _ ▸ hu)
  | true => exact absurd (searchEvent_update_of_true good hD hx u) hu

end event

/-! ## The projector onto a good value at a cell of a set -/

section orProj

variable (good : X → Y → Prop) [∀ z, DecidablePred (good z)] (Z : Finset X)

/-- At a cell of `Z`, the projector onto the values that are not good; elsewhere the identity. -/
noncomputable def noGood (x : X) : Matrix (Option Y) (Option Y) ℂ :=
  if x ∈ Z then 1 - cellGood (good x) else 1

/-- The indicator that a database holds a good value at a cell of `Z`. -/
def orFn (D : Database X Y) : ℂ :=
  if ∃ z ∈ Z, ∃ y, D z = some y ∧ good z y then 1 else 0

/-- The projector onto the databases holding a good value at a cell of `Z`. -/
noncomputable def orProj : Matrix (Database X Y) (Database X Y) ℂ :=
  1 - piKron (noGood good Z)

theorem noGood_eq_diagonal (x : X) :
    noGood good Z x = diagonal fun o ↦ if x ∈ Z then 1 - cellGoodFn (good x) o else 1 := by
  by_cases hx : x ∈ Z
  · simp [noGood, hx, cellGood, ← diagonal_one, diagonal_sub]
  · simp [noGood, hx]

/-- A pi-tensor product of diagonal matrices is diagonal. -/
theorem piKron_diagonal {ι Z' : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Z']
    (d : ι → Z' → ℂ) :
    piKron (fun i ↦ diagonal (d i)) = diagonal fun D ↦ ∏ i, d i (D i) := by
  ext D D'
  by_cases h : D = D'
  · subst h
    simp only [piKron_apply, diagonal_apply_eq]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [piKron_apply, diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (diagonal_apply_ne _ hi)

theorem orProj_eq_diagonal : orProj good Z = diagonal (orFn good Z) := by
  rw [orProj, show noGood good Z = fun x ↦ diagonal fun o ↦
      if x ∈ Z then 1 - cellGoodFn (good x) o else 1 from funext (noGood_eq_diagonal good Z),
    piKron_diagonal, ← diagonal_one, diagonal_sub]
  congr 1
  funext D
  by_cases h : ∃ z ∈ Z, ∃ y, D z = some y ∧ good z y
  · obtain ⟨z, hz, y, hy, hg⟩ := h
    have hc : ∃ z ∈ Z, ∃ y, D z = some y ∧ good z y := ⟨z, hz, y, hy, hg⟩
    simp only [orFn, hc, ↓reduceIte]
    rw [Finset.prod_eq_zero (Finset.mem_univ z)]
    · simp
    · simp [hz, hy, cellGoodFn, hg]
  · simp only [orFn, h, ↓reduceIte]
    rw [Finset.prod_eq_one]
    · simp
    · intro x _
      by_cases hx : x ∈ Z
      · rcases hD : D x with _ | y
        · simp [hx, cellGoodFn]
        · have : ¬ good x y := fun hg ↦ h ⟨x, hx, y, hD, hg⟩
          simp [hx, cellGoodFn, this]
      · simp [hx]

theorem orFn_mem (D : Database X Y) : orFn good Z D = 0 ∨ orFn good Z D = 1 := by
  unfold orFn
  split_ifs <;> simp

variable [Nonempty Y]

theorem norm_noGood_le (x : X) : ‖noGood good Z x‖ ≤ 1 := by
  rw [noGood_eq_diagonal, l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun o ↦ ?_
  by_cases hx : x ∈ Z
  · rcases cellGoodFn_mem (good x) o with h | h <;> simp [hx, h]
  · simp [hx]

theorem norm_cellCompress_le : ‖cellCompress Y‖ ≤ 1 :=
  l2_opNorm_le_one_of_conjTranspose_mul_self (by
    rw [conjTranspose_cellCompress, cellCompress_mul_self])

/-- Compressing every cell conjugates `orProj` into a pi-tensor product. -/
theorem compress_orProj :
    compressAll X Y * orProj good Z * compressAll X Y =
      1 - piKron (fun x ↦ cellCompress Y * noGood good Z x * cellCompress Y) := by
  rw [orProj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, compressAll_mul_self, compressAll,
    piKron_mul, piKron_mul]

/-- **The compressed projector is close to the projector.** -/
theorem norm_compress_orProj_sub_le (s : ℕ) (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s) :
    ‖compressAll X Y * orProj good Z * compressAll X Y - orProj good Z‖ ≤
      Z.card * (2 * √((s : ℝ) / Fintype.card Y)) := by
  rw [compress_orProj, orProj, sub_sub_sub_cancel_left]
  have hc := norm_cellCompress_le (Y := Y)
  refine (norm_piKron_sub_le _ _ (fun x ↦ norm_noGood_le good Z x) (fun x ↦ ?_)).trans ?_
  · calc ‖cellCompress Y * noGood good Z x * cellCompress Y‖
        ≤ ‖cellCompress Y‖ * ‖noGood good Z x‖ * ‖cellCompress Y‖ :=
          (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
            (norm_nonneg _))
      _ ≤ 1 * 1 * 1 := by gcongr; exact norm_noGood_le good Z x
      _ = 1 := by norm_num
  · have hcell : ∀ x, ‖noGood good Z x - cellCompress Y * noGood good Z x * cellCompress Y‖ ≤
        if x ∈ Z then 2 * √((s : ℝ) / Fintype.card Y) else 0 := by
      intro x
      by_cases hx : x ∈ Z
      · have hid : (1 - cellGood (good x)) - cellCompress Y * (1 - cellGood (good x)) *
            cellCompress Y = cellCompress Y * cellGood (good x) * cellCompress Y -
              cellGood (good x) := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, cellCompress_mul_self]
          abel
        simp only [hx, ↓reduceIte, noGood]
        rw [hid]
        refine (norm_conj_cellGood_sub_le (good x)).trans ?_
        have hle : ((Finset.univ.filter (good x)).card : ℝ) / Fintype.card Y ≤
            (s : ℝ) / Fintype.card Y :=
          div_le_div_of_nonneg_right (by exact_mod_cast hs x) (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (by norm_num)
      · simp [noGood, hx, cellCompress_mul_self]
    calc ∑ x, ‖noGood good Z x - cellCompress Y * noGood good Z x * cellCompress Y‖
        ≤ ∑ x, (if x ∈ Z then 2 * √((s : ℝ) / Fintype.card Y) else 0) :=
          Finset.sum_le_sum fun x _ ↦ hcell x
      _ = Z.card * (2 * √((s : ℝ) / Fintype.card Y)) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

end orProj

end Qrom
