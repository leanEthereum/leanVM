module

public import LeanVM.Cost.Bounds.PMCore.LeafOps
public import LeanVM.Cost.Bounds.PMCore.LeafRank
public import LeanVM.Protocol.Extraction.Fast.PMBasis.DegreeRecursion
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeafSpan
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf

public import LeanVM.Cost.Bounds.PMLane.InterpDefs
/-!
# Bounds: the leaf's pivot table, by the rank potential

`insertKernelLeafPivotRowWithFuel` (CompPoly, `KernelLeaf.lean`) inserts a row into a table of
rows indexed by shifted leading position: at a conflict it cancels the leading term of the row
(or of the table's row, which the new row then replaces) and goes on with the result. On rows
`X^e·v`, `e ≤ 1`, of width `r` (`TableInv`), every cancellation lowers the rank potential `Φ` (the
table rows' ranks `rk` plus the carried row's, `LeafRank.lean`), so
**`insertPivotC_cost`**: `price + c·Φ(after) ≤ c·(Φ(before) + rk(row)) + c`, `c = stepPrice r` the
price of one step (two leading terms, a cancellation, a slot written).
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open LeanVM.Extraction.Fast.PMDegree (HomRowLe homRowLe_cancel)

public section

/-- The rank of a slot: `0` when empty. -/
@[expose] def rkOpt (r : ℕ) (shift : Array ℕ) (o : Option (PolynomialRow K)) : ℕ :=
  o.elim 0 (rk r shift)

/-- **The potential of a table**: its rows' ranks. -/
@[expose] def phi (r : ℕ) (shift : Array ℕ) (T : Array (Option (PolynomialRow K))) : ℕ :=
  (T.toList.map (rkOpt r shift)).sum

/-- The table's rows: width `r`, `X^e·v` with `e ≤ 1`, each at the slot of its leading position. -/
@[expose] def TableInv (r : ℕ) (shift : Array ℕ) (T : Array (Option (PolynomialRow K))) : Prop :=
  T.size = r ∧ ∀ p q, T.getD p none = some q →
    q.size = r ∧ HomRowLe 1 q ∧ rowShiftedLeadingPosition? q shift = some p

theorem list_sum_set {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) (p : ℕ) (x : α) (d : α), p < l.length →
      ((l.set p x).map f).sum + f (l.getD p d) = (l.map f).sum + f x
  | [], _, _, _, h => by simp at h
  | y :: l, 0, x, d, _ => by simp; omega
  | y :: l, p + 1, x, d, h => by
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getD_cons_succ]
    have := list_sum_set f l p x d (by simpa using h)
    omega

theorem phi_set (r : ℕ) (shift : Array ℕ) (T : Array (Option (PolynomialRow K))) {p : ℕ}
    (hp : p < T.size) (x : Option (PolynomialRow K)) :
    phi r shift (T.setIfInBounds p x) + rkOpt r shift (T.getD p none) =
      phi r shift T + rkOpt r shift x := by
  unfold phi
  rw [Array.toList_setIfInBounds]
  have := list_sum_set (rkOpt r shift) T.toList p x none (by simpa using hp)
  rw [List.getD_eq_getElem?_getD] at this
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList]
  exact this

theorem rowWithin_of_homRow {r : ℕ} {row : PolynomialRow K} (hs : row.size = r)
    (hh : HomRowLe 1 row) : RowWithin r 2 row := by
  refine ⟨hs.le, fun e he ↦ ?_⟩
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
  have h1 := hh.natDegree_le j
  have h2 := LeanVM.Extraction.Fast.PMDegree.val_size_le_natDegree_add_one row[j]
  rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] at h1
  simp only [Option.getD_some] at h1
  omega

theorem tableInv_set {r : ℕ} {shift : Array ℕ} {T : Array (Option (PolynomialRow K))}
    (hT : TableInv r shift T) {p : ℕ} {row : PolynomialRow K} (hs : row.size = r)
    (hh : HomRowLe 1 row) (hpos : rowShiftedLeadingPosition? row shift = some p) :
    TableInv r shift (T.setIfInBounds p (some row)) := by
  refine ⟨by simp [hT.1], fun p' q hq ↦ ?_⟩
  rw [DenseMatrix.array_getD_setIfInBounds] at hq
  split_ifs at hq with h
  · cases hq; obtain ⟨rfl, -⟩ := h; exact ⟨hs, hh, hpos⟩
  · exact hT.2 p' q hq

variable (P : MachineProgram)

/-- **One insertion into the pivot table** (`insertKernelLeafPivotRowWithFuel`, any fuel): rows
`X^e·v` of width `r`, shifts at most `S`. -/
theorem insertPivotC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.insertKernelLeafPivotRowWithFuel.c531.costDeps)
    {r S : ℕ} (hr : r < 2 ^ 40) (hS40 : S < 2 ^ 60) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    ∀ (fuel : ℕ) (T : Array (Option (PolynomialRow K))) (row : PolynomialRow K), fuel < 2 ^ 128 →
      TableInv r shift T → row.size = r → HomRowLe 1 row →
      machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.insertKernelLeafPivotRowWithFuel.c531.costIdx
          [encodeValue fuel, encodeValue T, encodeValue shift, encodeValue row] +
          stepPrice r * phi r shift (insertKernelLeafPivotRowWithFuel fuel T shift row) ≤
        stepPrice r * (phi r shift T + rk r shift row) + stepPrice r ∧
      TableInv r shift (insertKernelLeafPivotRowWithFuel fuel T shift row) := by
  intro fuel
  induction fuel with
  | zero =>
    intro T row _ hT _ _
    rw [Auto.CompPoly.PolynomialMatrix.Approximant.insertKernelLeafPivotRowWithFuel.c531.costEq P hP]
    simp only [insertKernelLeafPivotRowWithFuel, limbs_zero, Nat.rec_zero]
    refine ⟨?_, hT⟩
    have : stepPrice r * phi r shift T ≤ stepPrice r * (phi r shift T + rk r shift row) :=
      Nat.mul_le_mul_left _ (by omega)
    unfold stepPrice at *
    omega
  | succ k ih =>
    intro T row hk hT hrs hrh
    rw [Auto.CompPoly.PolynomialMatrix.Approximant.insertKernelLeafPivotRowWithFuel.c531.costEq P hP]
    have hl := limbs_le_two (show k + 1 < 2 ^ 128 by omega)
    have hRw := rowWithin_of_homRow hrs hrh
    have hLTr := rowShiftedLeadingTerm_cost P (by includes) (C := r) (D := 2) (S := S) (by omega)
      (by omega) row hRw shift hS
    have hmono : ∀ a b, a ≤ b → stepPrice r * a ≤ stepPrice r * b := fun a b h ↦ Nat.mul_le_mul_left _ h
    have hspl : ∀ a, stepPrice r * (a + 1) = stepPrice r * a + stepPrice r := fun a ↦ by ring
    dsimp only
    rw [insertKernelLeafPivotRowWithFuel]
    generalize hlt : rowShiftedLeadingTerm? row shift = olt
    cases olt with
    | none =>
      dsimp only
      refine ⟨?_, hT⟩
      have := hmono (phi r shift T) (phi r shift T + rk r shift row) (by omega)
      unfold stepPrice at *
      omega
    | some t =>
      dsimp only
      obtain ⟨hdt, hpt, -, -, hsdt, -⟩ := rowShiftedLeadingTerm?_some_data hlt
      have htp : t.position < r := by
        have := PolynomialMatrix.rowShiftedLeadingPosition?_lt hpt; omega
      have hTs := hT.1
      generalize hslot : T.getD t.position none = os
      cases os with
      | none =>
        dsimp only
        have hphi := phi_set r shift T (p := t.position) (by omega) (some row)
        rw [hslot] at hphi
        simp only [rkOpt, Option.elim_none, Option.elim_some, Nat.add_zero] at hphi
        refine ⟨?_, tableInv_set hT hrs hrh hpt⟩
        rw [hphi]
        unfold stepPrice at *
        omega
      | some piv =>
        dsimp only
        obtain ⟨hps, hph, hpp⟩ := hT.2 _ _ hslot
        have hPw := rowWithin_of_homRow hps hph
        have hLTp := rowShiftedLeadingTerm_cost P (by includes) (C := r) (D := 2) (S := S) (by omega)
          (by omega) piv hPw shift hS
        generalize hlt2 : rowShiftedLeadingTerm? piv shift = olt2
        cases olt2 with
        | none =>
          dsimp only
          have hphi := phi_set r shift T (p := t.position) (by omega) (some row)
          rw [hslot] at hphi
          simp only [rkOpt, Option.elim_some] at hphi
          refine ⟨?_, tableInv_set hT hrs hrh hpt⟩
          have := hmono (phi r shift (T.setIfInBounds t.position (some row)))
            (phi r shift T + rk r shift row) (by omega)
          unfold stepPrice at *
          omega
        | some t2 =>
          dsimp only
          obtain ⟨hdt2, hpt2, -, -, hsdt2, -⟩ := rowShiftedLeadingTerm?_some_data hlt2
          have hpos : t2.position = t.position := by rw [hpp] at hpt2; exact (Option.some.inj hpt2).symm
          have hsd1 : t.shiftedDegree < 2 ^ 64 := by
            have := rowShiftedDegree?_le hRw hS hdt; omega
          have hsd2 : t2.shiftedDegree < 2 ^ 64 := by
            have := rowShiftedDegree?_le hPw hS hdt2; omega
          rw [limbs_of_lt hsd1, limbs_of_lt hsd2]
          simp only [max_self]
          split_ifs with hlt'
          · -- the new row takes the slot; the table's row is cancelled and carried on
            have hc := cancelKernelLeafLeadingTermC_cost P (by includes) (C := r) (D := 2) (S := S)
              (by omega) (by omega) (by omega) piv row hPw hRw shift hS
            have hnh : HomRowLe 1 (cancelKernelLeafLeadingTerm piv row shift) :=
              homRowLe_cancel hph hrh fun a b ha hb ↦ by
                rw [hlt2] at ha; rw [hlt] at hb; cases ha; cases hb; omega
            have hns : (cancelKernelLeafLeadingTerm piv row shift).size = r := by
              rw [cancelKernelLeafLeadingTerm_size (by rw [hrs, hps])]; exact hps
            have hT' := tableInv_set hT hrs hrh hpt
            obtain ⟨hcost, hinv⟩ := ih (T.setIfInBounds t.position (some row))
              (cancelKernelLeafLeadingTerm piv row shift) (by omega) hT' hns hnh
            have hmeas := cancelKernelLeafLeadingTerm_shiftedRowMeasure_lt hlt2 hlt hpos hlt'.le
              (by rw [hrs, hps])
            have hrk := rk_lt (r := r) hmeas (measure_mem_of_leadingTerm hps hph hlt2)
            have hphi := phi_set r shift T (p := t.position) (by omega) (some row)
            rw [hslot] at hphi
            simp only [rkOpt, Option.elim_some] at hphi
            refine ⟨?_, hinv⟩
            have := hmono (phi r shift (T.setIfInBounds t.position (some row)) +
              rk r shift (cancelKernelLeafLeadingTerm piv row shift) + 1)
              (phi r shift T + rk r shift row) (by omega)
            rw [hspl] at this
            unfold stepPrice at *
            omega
          · -- the row is cancelled by the table's row and carried on
            have hc := cancelKernelLeafLeadingTermC_cost P (by includes) (C := r) (D := 2) (S := S)
              (by omega) (by omega) (by omega) row piv hRw hPw shift hS
            have hnh : HomRowLe 1 (cancelKernelLeafLeadingTerm row piv shift) :=
              homRowLe_cancel hrh hph fun a b ha hb ↦ by
                rw [hlt] at ha; rw [hlt2] at hb; cases ha; cases hb; omega
            have hns : (cancelKernelLeafLeadingTerm row piv shift).size = r := by
              rw [cancelKernelLeafLeadingTerm_size (by rw [hrs, hps])]; exact hrs
            obtain ⟨hcost, hinv⟩ := ih T (cancelKernelLeafLeadingTerm row piv shift) (by omega) hT
              hns hnh
            have hmeas := cancelKernelLeafLeadingTerm_shiftedRowMeasure_lt hlt hlt2 hpos.symm
              (by omega) (by rw [hrs, hps])
            have hrk := rk_lt (r := r) hmeas (measure_mem_of_leadingTerm hrs hrh hlt)
            refine ⟨?_, hinv⟩
            have := hmono (phi r shift T + rk r shift (cancelKernelLeafLeadingTerm row piv shift) + 1)
              (phi r shift T + rk r shift row) (by omega)
            rw [hspl] at this
            unfold stepPrice at *
            omega

end

end LeanVM.Cost.Bounds.PMCore
