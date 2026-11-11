module

public import LeanVM.Cost.Bounds.PMSolve.Small
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Basic
public import LeanVM.Cost.Bounds.PMLane.InterpDefs

/-!
# Bounds: the certified problem's lift, compiled

`fullWindowExactNullspaceProblem fftModContext equation bound` (`fullWindowProblemC`): the orders
`deg M_b + bound + 2`, and the lift `reducedExactNullspaceLift`: each relation entry reduced modulo
its column's modulus, then `−diag(M)`. On the Guruswami–Sudan data the entries are reduced already
(`natDegree_gsRelationMatrix_entry_lt`, `Fast/PMShape.lean`), so each remainder takes the reversal
remainder's first branch: its guard reads both operands (`modByMonicFFTC_first_cost`, `≤ 42·|p| +
63·|q| + 82`), no product.

**`fullWindowProblemC_cost`**: on `w` relation rows, `m` monic moduli of at most `Q` coefficients,
entries shorter than their column's modulus: at most `liftPrice Q w m`.
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

open LeanVM.Cost.Auto.CompPoly.PolynomialMatrix.Approximant LeanVM.Cost.Auto.CompPoly.PolynomialMatrix

public section

variable (P : MachineProgram)

theorem cpoly_trim_eq (p : CPolynomial K) : p.val.trim = p.val :=
  CPolynomial.Raw.Trim.trim_eq_of_isCanonical p.property

/-- **The reversal remainder's first branch** (`modByMonicFFTC`, the dividend shorter than the
monic modulus): the guard reads both, at most `42·|p| + 63·|q| + 82`. -/
theorem modByMonicFFTC_first_cost (hP : Includes P modByMonicFFTC.costDeps) (p q : CPolynomial K)
    (hq : q.monic = true) (hpq : p.val.size < q.val.size) (hqs : q.val.size < 2 ^ 60) :
    machineCost P modByMonicFFTC.costIdx [encodeValue p, encodeValue q] ≤
      42 * p.val.size + 63 * q.val.size + 82 := by
  rw [modByMonicFFTC.costEq P hP, Auto.CompPoly.CPolynomial.Raw.modByMonicByReversal.c421.costEq P
    (by includes)]
  have hpt := cpoly_trim_eq p
  have hqt := cpoly_trim_eq q
  have hlc : (CPolynomial.Raw.leadingCoeff q.val == 1) = true := by
    simpa [CPolynomial.monic, CPolynomial.leadingCoeff, CPolynomial.Raw.leadingCoeff, hqt] using hq
  have := trimLen_cost P (by includes) p.val p.val.size (by omega)
  have := trimLen_cost P (by includes) q.val q.val.size (by omega)
  have := listBeqK_cost P (by includes) p.val.toList p.val.toList
  have := listBeqK_cost P (by includes) q.val.toList q.val.toList
  have := getLastDC_cost P (by includes) q.val 0 (by omega)
  have h1 : (Array.extract p.val 0 (CompPolyLib.trimLen p.val p.val.size)).size ≤ p.val.size := by
    simp
  have h2 : (Array.extract q.val 0 (CompPolyLib.trimLen q.val q.val.size)).size ≤ q.val.size := by
    simp
  have hp64 : p.val.size < 2 ^ 64 := by omega
  have hq64 : q.val.size < 2 ^ 64 := by omega
  simp only [hpt, hqt, beq_self_eq_true, Bool.true_and, hlc, ↓reduceIte, hpq, Array.length_toList]
    at *
  rw [limbs_of_lt hp64, limbs_of_lt hq64]
  omega

/-- The lift's entry (`reducedExactNullspaceLift.c557.lam0`): an entry read and reduced on the
first branch, at most `123·Q + 77` for moduli of at most `Q` coefficients. -/
theorem liftEntryC_cost (hP : Includes P reducedExactNullspaceLift.c557.lam0.costDeps)
    (equation : ModularEquation K) (i j : ℕ) {Q : ℕ} (hQ : Q < 2 ^ 60)
    (hq : (equation.moduli.getD j 0).monic = true)
    (hqQ : (equation.moduli.getD j 0).val.size ≤ Q)
    (hred : (rowGet (equation.matrix.getD i #[]) j).val.size <
      (equation.moduli.getD j 0).val.size) :
    machineCost P reducedExactNullspaceLift.c557.lam0.costIdx
        [encodeValue equation, encodeValue i, encodeValue j] ≤ 123 * Q + 77 := by
  rw [reducedExactNullspaceLift.c557.lam0.costEq P hP, modByMonicWith.c559.costEq P (by includes)]
  have := rowGet_cost P (by includes) (equation.matrix.getD i #[]) j
  have := listBeqK_cost P (by includes) (equation.moduli.getD j 0).val.toList
    (↑(0 : CPolynomial K) : Array K).toList
  have := modByMonicFFTC_first_cost P (by includes) _ _ hq hred (by omega)
  have hz : (↑(0 : CPolynomial K) : Array K).size = 0 := rfl
  simp only [Array.length_toList, hz] at *
  split <;> omega

/-- `−diag(M)`'s entry: at most `18·Q + 16`. -/
theorem negDiagEntryC_cost (hP : Includes P negativeDiagonalRows.c561.lam0.costDeps)
    (moduli : Array (CPolynomial K)) (i j : ℕ) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) {Q : ℕ}
    (hqQ : (moduli.getD i 0).val.size ≤ Q) :
    machineCost P negativeDiagonalRows.c561.lam0.costIdx
        [encodeValue moduli, encodeValue i, encodeValue j] ≤ 18 * Q + 16 := by
  rw [negativeDiagonalRows.c561.lam0.costEq P hP]
  have hl := fun a ↦ RunsApp.of_spec (us := []) (vs := [encodeValue a])
    (Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costSpec P (by includes) a)
  have := map_cost P (by includes) _ (.closure Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costIdx [])
    hl 1 (↑(moduli.getD i 0) : Array K).toList (fun a _ ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil]
      rw [Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costEq P (by includes)])
  simp only [Array.length_toList, List.length_map] at *
  cost_simp
  split <;> omega


/-- The sizes the lift's price reads: `w` relation rows, `m` monic moduli of at most `Q`
coefficients, each entry shorter than its column's modulus. -/
@[expose] def LiftSizes (equation : ModularEquation K) (w m Q : ℕ) : Prop :=
  equation.matrix.size = w ∧ equation.moduli.size = m ∧ w < 2 ^ 29 ∧ m < 2 ^ 29 ∧ Q < 2 ^ 60 ∧
    (∀ j < m, (equation.moduli.getD j 0).monic = true ∧ (equation.moduli.getD j 0).val.size ≤ Q) ∧
    ∀ i < w, ∀ j < m, (rowGet (equation.matrix.getD i #[]) j).val.size <
      (equation.moduli.getD j 0).val.size

theorem ofFn_size_eq (rows width : ℕ) (e : ℕ → ℕ → CPolynomial K) :
    (PolynomialMatrix.ofFn rows width e).size = rows := by
  simp [PolynomialMatrix.ofFn]

/-- **The lift** (`reducedExactNullspaceLift`): at most
`w·(m·(123·Q + 113) + 49) + m·(m·(18·Q + 52) + 49) + w + m + 62`. -/
theorem reducedLiftC_cost (hP : Includes P reducedExactNullspaceLift.c557.costDeps)
    (equation : ModularEquation K) {w m Q : ℕ} (hs : LiftSizes equation w m Q) :
    machineCost P reducedExactNullspaceLift.c557.costIdx [encodeValue equation] ≤
      w * (m * (123 * Q + 113) + 49) + m * (m * (18 * Q + 52) + 49) + w + m + 62 := by
  obtain ⟨hw, hm, hw30, hm30, hQ, hmod, hred⟩ := hs
  rw [reducedExactNullspaceLift.c557.costEq P hP,
    ModularEquation.solutionWidth.c549.costEq P (by includes),
    ModularEquation.modularWidth.c560.costEq P (by includes),
    negativeDiagonalRows.c561.costEq P (by includes)]
  have hsW : equation.solutionWidth = w := hw
  have hmW : equation.modularWidth = m := hm
  have he1 := fun i j ↦ RunsApp.of_spec (us := [encodeValue equation])
    (vs := [encodeValue i, encodeValue j])
    (reducedExactNullspaceLift.c557.lam0.costSpec P (by includes) equation i j)
  have h1 := ofFnC_cost P (by includes) equation.solutionWidth equation.modularWidth
    (by omega) (by omega) _ (.closure reducedExactNullspaceLift.c557.lam0.costIdx
      [encodeValue equation]) he1 (123 * Q + 78) (fun i hi j hj ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [hsW] at hi
      rw [hmW] at hj
      have := liftEntryC_cost P (by includes) equation i j (by omega) (hmod j hj).1 (hmod j hj).2
        (hred i hi j hj)
      omega)
  have he2 := fun i j ↦ RunsApp.of_spec (us := [encodeValue equation.moduli])
    (vs := [encodeValue i, encodeValue j])
    (negativeDiagonalRows.c561.lam0.costSpec P (by includes) equation.moduli i j)
  have h2 := ofFnC_cost P (by includes) equation.moduli.size equation.moduli.size
    (by omega) (by omega) _ (.closure negativeDiagonalRows.c561.lam0.costIdx
      [encodeValue equation.moduli]) he2 (18 * Q + 17) (fun i hi j hj ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have := negDiagEntryC_cost P (by includes) equation.moduli i j (by omega) (by omega)
        (hmod i (by omega)).2
      omega)
  simp only [hsW, hmW] at h1 ⊢
  simp only [hm] at h2 ⊢
  have hz1 := ofFn_size_eq equation.solutionWidth equation.modularWidth
    (fun i j ↦ modByMonicWith FFT.fftModContext (rowGet (equation.matrix.getD i #[]) j)
      (equation.moduli.getD j 0))
  have hz2 : (negativeDiagonalRows equation.moduli).size = equation.moduli.size :=
    ofFn_size_eq _ _ _
  rw [hsW, hmW] at hz1
  rw [hm] at hz2
  rw [hz1, hz2]
  have e1 : w * (m * (123 * Q + 78 + 35) + 49) = w * (m * (123 * Q + 113) + 49) := by ring
  have e2 : m * (m * (18 * Q + 17 + 35) + 49) = m * (m * (18 * Q + 52) + 49) := by ring
  omega

/-- **The certified problem** (`fullWindowExactNullspaceProblem fftModContext`): the orders and
the lift, at most `liftPrice Q w m`. -/
theorem fullWindowProblemC_cost (hP : Includes P fullWindowProblemC.costDeps)
    (equation : ModularEquation K) (bound : ℕ) (hb : bound < 2 ^ 62) {w m Q : ℕ}
    (hs : LiftSizes equation w m Q) :
    machineCost P fullWindowProblemC.costIdx [encodeValue equation, encodeValue bound] ≤
      liftPrice Q w m := by
  have hs' := hs
  obtain ⟨hw, hm, hw30, hm30, hQ, hmod, hred⟩ := hs'
  rw [fullWindowProblemC.costEq P hP]
  have := reducedLiftC_cost P (by includes) equation hs
  have hl := fun M ↦ RunsApp.of_spec (us := [encodeValue bound]) (vs := [encodeValue M])
    (fullWindowProblemC.lam0.costSpec P (by includes) bound M)
  have := map_cost P (by includes) _ (.closure fullWindowProblemC.lam0.costIdx [encodeValue bound])
    hl 21 equation.moduli.toList (fun M hM ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [fullWindowProblemC.lam0.costEq P (by includes)]
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hM
      have hj' : j < m := by simpa [hm] using hj
      have hsz := (hmod j hj').2
      have hget : equation.moduli.getD j 0 = equation.moduli.toList[j] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj)]
        simp
      rw [hget] at hsz
      have := natDegree_cost P (by includes) equation.moduli.toList[j] (by omega)
      have := natDegree_le_size equation.moduli.toList[j]
      cost_simp
      omega)
  simp only [Array.length_toList, List.length_map] at *
  unfold liftPrice
  rw [hm]
  omega

end

end LeanVM.Cost.Bounds.PMSolve
