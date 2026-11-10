module

public import LeanVM.Cost.Bounds.Decoder.Roots
public import LeanVM.Cost.Bounds.Decoder.Rows
public import LeanVM.Cost.Extractor.PMLane
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PartialLinearization

/-!
# Bounds: the certified solve's small pieces, compiled

The prices of the pieces of `certifiedSolutionBasis` (`Fast/CertifiedSolve.lean`, compiled in
`Cost/Extractor/PMSolve.lean`) besides the lift and the PM-basis:

* the guard (`certifiedGuardC_cost`: a monic test per modulus);
* the expanded shift (`exactNullspaceShiftC_cost`);
* a row's certificate (`certifiedRowC_cost`: its size and its shifted degree);
* the principal parts (`principalSolutionRowsC_cost`).
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.CompPoly.PolynomialMatrix.Approximant LeanVM.Cost.Auto.CompPoly.PolynomialMatrix

public section

variable (P : MachineProgram)

/-- `monic` of a polynomial of word-sized size: at most `15`. -/
theorem monicC_cost (hP : Includes P Auto.CompPoly.CPolynomial.monic.c553.costDeps)
    (p : CPolynomial K) (hp : p.val.size < 2 ^ 64) :
    machineCost P Auto.CompPoly.CPolynomial.monic.c553.costIdx [encodeValue p] ≤ 15 := by
  rw [Auto.CompPoly.CPolynomial.monic.c553.costEq P hP,
    Auto.CompPoly.CPolynomial.leadingCoeff.c554.costEq P (by includes)]
  have := getLastDC_cost P (by includes) p.val 0 hp
  omega

/-- **The guard** (`certifiedGuard`): a monic test per modulus, at most `49·m + 59`. -/
theorem certifiedGuardC_cost (hP : Includes P certifiedGuardC.costDeps)
    (equation : ModularEquation K) (shift : Array ℕ)
    (hm : equation.moduli.size < 2 ^ 62) (hw : equation.solutionWidth < 2 ^ 64)
    (hs : shift.size < 2 ^ 64) (hM : equation.matrix.size < 2 ^ 64)
    (hMW : MatrixWidth equation.matrix < 2 ^ 64)
    (hq : ∀ b, (equation.moduli.getD b 0).val.size < 2 ^ 64) :
    machineCost P certifiedGuardC.costIdx [encodeValue equation, encodeValue shift] ≤
      49 * equation.moduli.size + 59 := by
  rw [certifiedGuardC.costEq P hP, ModularEquation.solutionWidth.c551.costEq P (by includes)]
  have := matrixWidthC_cost P (by includes) equation.matrix hM
  have := rangeLoop_cost P (by includes) equation.moduli.size [] (by omega)
  have hl := fun b ↦ RunsApp.of_spec (us := [encodeValue equation]) (vs := [encodeValue b])
    (certifiedGuardC.lam0.costSpec P (by includes) equation b)
  have := all_cost P (by includes) _ (.closure certifiedGuardC.lam0.costIdx [encodeValue equation])
    hl 23 (List.range equation.moduli.size) (fun b _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [certifiedGuardC.lam0.costEq P (by includes)]
      have := monicC_cost P (by includes) _ (hq b)
      omega)
  simp only [List.length_range] at this
  cost_simp
  split_ifs <;> omega

/-- **The expanded shift** (`exactNullspaceShift`): at most `25·|shift| + 2·q + 16`. -/
theorem exactNullspaceShiftC_cost (hP : Includes P exactNullspaceShiftC.costDeps)
    (shift : Array ℕ) (quotientWidth delta : ℕ) (hd : delta + 1 < 2 ^ 63)
    (hv : ∀ x ∈ shift.toList, x < 2 ^ 63) :
    machineCost P exactNullspaceShiftC.costIdx
        [encodeValue shift, encodeValue quotientWidth, encodeValue delta] ≤
      25 * shift.size + 2 * quotientWidth + 16 := by
  rw [exactNullspaceShiftC.costEq P hP]
  have hl := fun x ↦ RunsApp.of_spec (us := [encodeValue shift, encodeValue delta])
    (vs := [encodeValue x]) (exactNullspaceShiftC.lam0.costSpec P (by includes) shift delta x)
  have := map_cost P (by includes) _ (.closure exactNullspaceShiftC.lam0.costIdx
    [encodeValue shift, encodeValue delta]) hl 7 shift.toList (fun x hx ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [exactNullspaceShiftC.lam0.costEq P (by includes)]
      have := hv x hx
      unfold principalShiftOffset
      cost_simp
      omega)
  simp only [Array.length_toList, List.length_map, Array.size_replicate] at *
  have hlp : (liftedPrincipalShift shift delta).size = shift.size := by
    simp [liftedPrincipalShift]
  rw [hlp]
  omega

/-- **A row's certificate** (`certifiedRow`): its size, then its shifted degree, at most
`84·C + 40` for a row of at most `C` entries of at most `D` coefficients, shifts at most `S`. -/
theorem certifiedRowC_cost (hP : Includes P certifiedRowC.costDeps) {C D S : ℕ}
    (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (width : ℕ) (hwd : width < 2 ^ 64)
    (eShift : Array ℕ) (hS : ∀ j, eShift.getD j 0 ≤ S) (bound : ℕ) (hb : bound < 2 ^ 61)
    (row : PolynomialRow K) (hrow : RowWithin C D row) :
    machineCost P certifiedRowC.costIdx
        [encodeValue width, encodeValue eShift, encodeValue bound, encodeValue row] ≤
      84 * C + 40 := by
  rw [certifiedRowC.costEq P hP]
  have := rowShiftedDegree_cost P (by includes) hC hDS row hrow eShift hS
  have hsz := hrow.1
  have hv : ∀ v, rowShiftedDegree? row eShift = some v → v ≤ D + S :=
    fun v hv ↦ rowShiftedDegree?_le hrow hS hv
  generalize hr : rowShiftedDegree? row eShift = o at hv
  cases o with
  | none => cost_simp; split_ifs <;> omega
  | some v =>
    have := hv v rfl
    dsimp only
    cost_simp
    split_ifs <;> omega

/-- **The principal parts** (`principalSolutionRows`): `sW` entries read per row, at most
`(38·sW + 34)·|basis| + 10`. -/
theorem principalSolutionRowsC_cost (hP : Includes P principalSolutionRowsC.costDeps)
    (solutionWidth : ℕ) (hw : solutionWidth < 2 ^ 62) (basis : PolynomialMatrix K) :
    machineCost P principalSolutionRowsC.costIdx [encodeValue solutionWidth, encodeValue basis] ≤
      (38 * solutionWidth + 34) * basis.size + 10 := by
  rw [principalSolutionRowsC.costEq P hP]
  have hl := fun row ↦ RunsApp.of_spec (us := [encodeValue solutionWidth]) (vs := [encodeValue row])
    (principalSolutionRowsC.lam0.costSpec P (by includes) solutionWidth row)
  have := map_cost P (by includes) _ (.closure principalSolutionRowsC.lam0.costIdx
    [encodeValue solutionWidth]) hl (38 * solutionWidth + 17) basis.toList (fun row _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [principalSolutionRowsC.lam0.costEq P (by includes)]
      have := rangeLoop_cost P (by includes) solutionWidth [] (by omega)
      have hm := fun j ↦ RunsApp.of_spec (us := [encodeValue row]) (vs := [encodeValue j])
        (principalSolutionRowsC.lam0.lam0.costSpec P (by includes) row j)
      have := map_cost P (by includes) _ (.closure principalSolutionRowsC.lam0.lam0.costIdx
        [encodeValue row]) hm 9 (List.range solutionWidth) (fun j _ ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [principalSolutionRowsC.lam0.lam0.costEq P (by includes)]
          have := rowGet_cost P (by includes) row j
          omega)
      simp only [List.length_range, List.length_map] at *
      omega)
  simp only [Array.length_toList, List.length_map] at *
  have e : (38 * solutionWidth + 34) * basis.size =
      (38 * solutionWidth + 17 + 13) * basis.size + 4 * basis.size := by ring
  omega

end

end LeanVM.Cost.Bounds.PMSolve
