module

public import LeanVM.Cost.Bounds.PMSolve.Lift
public import LeanVM.Cost.Bounds.PMBasis.Defs
public import LeanVM.Protocol.Extraction.Fast.PMShape
public import LeanVM.Cost.Bounds.PMCore.Core
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Recursion
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PartialLinearization

public import LeanVM.Cost.Bounds.PMLane.InterpDefs
/-!
# Bounds: the certified solve, compiled

`certifiedSolutionBasis fftModContext (popovEvalPMBasisContext novelTransform fftMulContext
fftMulLowContext 1)` (`certifiedSolveC`, `Cost/Extractor/PMSolve.lean`): the guard, the
expanded shift and the certified problem (the compiled code evaluates both twice: the context's
`basis` reads its problem argument twice), the fuel (`maxOrder`), **the PM-basis core**
(`pmCoreC`, its price a hypothesis, `PMCoreCostAt`: `pmCoreC_cost`), each basis row's
certificate (a size and a shifted degree read), the principal parts.

The basis's sizes come from popov's core (`popovRuntime_core_spec`: as many rows as the problem,
each of the problem's width, entries of degree at most `max 1 o`); the problem's from the lift
(`liftProblem_sizes`: rows of width `m`, entries of at most `o` coefficients).

**`certifiedSolveC_cost`**: at most `certSolveCost p L Q w m o` (`o` the problem's maximal order).
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open LeanVM.Cost.Bounds.PMBasis

open LeanVM.Cost.Auto.CompPoly.PolynomialMatrix.Approximant LeanVM.Cost.Auto.CompPoly.PolynomialMatrix
open LeanVM.Cost.Auto.LeanVM.Extraction.Fast

public section

/-! ## The PM-basis core's price: a hypothesis  -/

/-- **The PM-basis core's price** (`pmCoreC`, `pmBasisWithFuelCore` on the target runtime at
`pmBasisFuel`), as the certified solve needs it: on a problem of `r` rows of width `m` with
pmcost's invariant (`PMCore.CoreInv r m SB`), at most the model's tree at the leaf price `L`,
`pmTree 1 L (pmNodePrice p r m) (maxOrder problem)` (`pmCoreC_cost`, `L` the
leaf's proved price plus its glue). -/
@[expose] def PMCoreCostAt (P : MachineProgram) (p : PMPrices) (L r m SB : ℕ) : Prop :=
  ∀ (problem : XAdicProblem K) (shift : Array ℕ), PMCore.CoreInv r m SB problem shift →
    machineCost P pmCoreC.costIdx
        [encodeValue (pmBasisFuel problem), encodeValue problem, encodeValue shift] ≤
      pmTree 1 L (pmNodePrice p r m) (maxOrder problem)

variable (P : MachineProgram)

/-! ## The fuel -/

theorem maxOrder_lt (problem : XAdicProblem K) (B : ℕ)
    (ho : ∀ x ∈ problem.orders.toList, x ≤ B) : maxOrder problem ≤ B := by
  unfold maxOrder
  rw [← Array.foldl_toList]
  have : ∀ (l : List ℕ) (acc : ℕ), acc ≤ B → (∀ x ∈ l, x ≤ B) → l.foldl max acc ≤ B := by
    intro l
    induction l with
    | nil => intro acc h _; exact h
    | cons a l ih =>
      intro acc h hl
      exact ih _ (max_le h (hl a (by simp))) (fun x hx ↦ hl x (by simp [hx]))
  exact this _ 0 (Nat.zero_le _) ho

/-- `pmBasisFuel`: at most `21·|orders| + 13`. -/
theorem pmBasisFuelC_cost (hP : Includes P pmBasisFuel.c569.costDeps) (problem : XAdicProblem K)
    (ho : ∀ x ∈ problem.orders.toList, x < 2 ^ 62) :
    machineCost P pmBasisFuel.c569.costIdx [encodeValue problem] ≤
      21 * problem.orders.size + 13 := by
  rw [pmBasisFuel.c569.costEq P hP]
  have := PMCore.maxOrderC_cost P (by includes) problem (fun x hx ↦ by
    have := ho x (Array.mem_toList_iff.2 hx); omega)
  have := maxOrder_lt problem (2 ^ 62) (fun x hx ↦ (ho x hx).le)
  cost_simp
  omega

/-! ## The certified problem's sizes -/

theorem size_modByMonicWith_le (modCtx : CPolynomial.ModContext K) (p : CPolynomial K)
    {M : CPolynomial K} (hM : M.monic = true) :
    (modByMonicWith modCtx p M).val.size ≤ M.natDegree := by
  have hMon : M.toPoly.Monic := (CPolynomial.monic_toPoly_iff M).1 hM
  by_cases hD : 1 ≤ M.natDegree
  · have := natDegree_modByMonicWith_lt modCtx p hMon hD
    have := LeanVM.Extraction.Fast.PMDegree.val_size_le_natDegree_add_one
      (modByMonicWith modCtx p M)
    omega
  · have hM1 : M.toPoly = 1 := by
      refine (Polynomial.Monic.natDegree_eq_zero hMon).1 ?_
      rw [← CPolynomial.natDegree_toPoly]
      omega
    have h0 : modByMonicWith modCtx p M = 0 := by
      apply CPolynomial.toPoly_injective
      rw [CompPoly.GuruswamiSudan.ApproximantBasis.modByMonicWith_toPoly modCtx hMon, hM1, Polynomial.modByMonic_one,
        CPolynomial.toPoly_zero]
    rw [h0]
    exact Nat.zero_le _

theorem size_neg_le (p : CPolynomial K) : (-p).val.size ≤ p.val.size := by
  show (CPolynomial.Raw.neg p.val).size ≤ _
  simp [CPolynomial.Raw.neg]

theorem mem_ofFn_entry {rows width : ℕ} {e : ℕ → ℕ → CPolynomial K} {row : PolynomialRow K}
    (hrow : row ∈ (PolynomialMatrix.ofFn rows width e).toList) {x : CPolynomial K}
    (hx : x ∈ row) : ∃ i < rows, ∃ j < width, x = e i j := by
  simp only [PolynomialMatrix.ofFn, List.toList_toArray, List.mem_map, List.mem_range] at hrow
  obtain ⟨i, hi, rfl⟩ := hrow
  simp only [List.mem_toArray, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨i, hi, j, hj, rfl⟩

/-- **The certified problem's sizes**: `m` orders `deg M_j + bound + 2`, rows of width `m`,
entries of at most `maxOrder` coefficients. -/
theorem liftProblem_sizes (equation : ModularEquation K) (bound : ℕ)
    (hmonic : ∀ j < equation.moduli.size, (equation.moduli.getD j 0).monic = true) :
    let prob := fullWindowExactNullspaceProblem FFT.fftModContext equation bound
    prob.orders.size = equation.moduli.size ∧
      (∀ row ∈ prob.matrix.toList, row.size = equation.moduli.size) ∧
      (∀ row ∈ prob.matrix.toList, ∀ e ∈ row, e.val.size ≤ maxOrder prob) ∧
      prob.matrix.size = equation.solutionWidth + equation.moduli.size := by
  intro prob
  have hord : ∀ j < equation.moduli.size,
      (equation.moduli.getD j 0).natDegree + bound + 2 ≤ maxOrder prob := by
    intro j hj
    have := LeanVM.Extraction.Fast.getD_le_foldl_max prob.orders j
    have hg : prob.orders.getD j 0 = (equation.moduli.getD j 0).natDegree + bound + 2 := by
      show (equation.moduli.map fun M ↦ M.natDegree + bound + 2).getD j 0 = _
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hj, Option.getD_some]
    rw [hg] at this
    exact this
  refine ⟨by simp [prob, fullWindowExactNullspaceProblem], ?_, ?_, ?_⟩
  · intro row hrow
    change row ∈ (reducedExactNullspaceLift FFT.fftModContext equation).toList at hrow
    rw [reducedExactNullspaceLift, negativeDiagonalRows, Array.toList_append,
      List.mem_append] at hrow
    rcases hrow with hr | hr <;> exact mem_ofFn_size hr
  · intro row hrow e he
    change row ∈ (reducedExactNullspaceLift FFT.fftModContext equation).toList at hrow
    rw [reducedExactNullspaceLift, negativeDiagonalRows, Array.toList_append,
      List.mem_append] at hrow
    rcases hrow with hr | hr
    · obtain ⟨i, -, j, hj, rfl⟩ := mem_ofFn_entry hr he
      have := size_modByMonicWith_le FFT.fftModContext (rowGet (equation.matrix.getD i #[]) j)
        (hmonic j hj)
      have := hord j hj
      omega
    · obtain ⟨i, hi, j, -, rfl⟩ := mem_ofFn_entry hr he
      have := hord i hi
      have hs := LeanVM.Extraction.Fast.PMDegree.val_size_le_natDegree_add_one
        (equation.moduli.getD i 0)
      have hn := size_neg_le (equation.moduli.getD i 0)
      generalize equation.moduli.getD i 0 = M at *
      split
      · omega
      · exact Nat.zero_le _
  · show (reducedExactNullspaceLift FFT.fftModContext equation).size = _
    rw [reducedExactNullspaceLift, Array.size_append, ofFn_size_eq, negativeDiagonalRows,
      ofFn_size_eq]


/-! ## The basis's sizes -/

/-- **The certified solve's basis** (popov's core on the evaluation-domain runtime): as many rows
as the problem, each of the problem's width, entries of degree at most `max 1 o`. -/
theorem certBasis_spec (prob : XAdicProblem K) (eShift : Array ℕ) :
    let B := (popovEvalPMBasisContext FFT.novelTransform FFT.fftMulContext FFT.fftMulLowContext
      1).basis prob eShift
    B.size = prob.matrix.size ∧ ∀ row ∈ B.toList, row.size = prob.matrix.size ∧
      ∀ j, (rowGet row j).natDegree ≤ max 1 (maxOrder prob) := by
  intro B
  have hB : B = pmBasisWithFuelCore (Popov.popovRuntime FFT.fftMulContext FFT.fftMulLowContext 1 1)
      (pmBasisFuel prob) prob eShift := by
    show pmBasisWithFuelCore (popovEvalRuntime _ _ _ _) _ _ _ = _
    rw [popovEvalRuntime_eq _ _ _ 1 1]
  obtain ⟨h1, -, h3⟩ := LeanVM.Extraction.Fast.PMDegree.popovRuntime_core_spec FFT.fftMulContext
    FFT.fftMulLowContext 1 (le_refl 1) (pmBasisFuel prob) prob eShift
    (by unfold pmBasisFuel; omega)
  rw [hB]
  exact ⟨h1, fun row hrow ↦ h3 row hrow⟩

theorem rowWithin_of_natDegree {row : PolynomialRow K} {C d : ℕ} (hsz : row.size ≤ C)
    (hd : ∀ j, (rowGet row j).natDegree ≤ d) : RowWithin C (d + 1) row := by
  refine ⟨hsz, fun e he ↦ ?_⟩
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
  have h := hd j
  have hg : rowGet row j = row[j] := by
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
  rw [hg] at h
  have := LeanVM.Extraction.Fast.PMDegree.val_size_le_natDegree_add_one row[j]
  omega

theorem certShift_getD_le (equation : ModularEquation K) (shift : Array ℕ) (bound : ℕ) {Sh : ℕ}
    (hSh : ∀ j, shift.getD j 0 ≤ Sh) (j : ℕ) :
    (certShift equation shift bound).getD j 0 ≤ Sh + bound + 1 := by
  unfold certShift exactNullspaceShift liftedPrincipalShift quotientShift principalShiftOffset
  rw [Array.getD_eq_getD_getElem?]
  rcases Nat.lt_or_ge j shift.size with hj | hj
  · rw [Array.getElem?_append_left (by simpa using hj)]
    have := hSh j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some] at this
    simp [Array.getElem?_eq_getElem hj]
    omega
  · rw [Array.getElem?_append_right (by simpa using hj)]
    simp only [Array.getElem?_replicate]
    split
    · simp only [Option.getD_some]; omega
    · simp

/-! ## The certified solve -/

variable (P : MachineProgram)

/-- **The certified solve, compiled** (`certifiedSolveC`): on `w` relation rows, `m` monic moduli
of at most `Q` coefficients, entries shorter than their modulus, a shift of `w` entries at most
`Sh`, at most `certSolveCost p L Q w m o`, `o` the certified problem's maximal order, given the
PM-basis core's price (`PMCoreCostAt P p L (w + m) m SB`). -/
theorem certifiedSolveC_cost (hP : Includes P certifiedSolveC.costDeps) (p : PMPrices)
    {L w m Q Sh SB : ℕ} (hcore : PMCoreCostAt P p L (w + m) m SB) (equation : ModularEquation K)
    (shift : Array ℕ) (bound : ℕ) (hs : LiftSizes equation w m Q)
    (hMW : MatrixWidth equation.matrix < 2 ^ 64)
    (hshift : shift.size = w) (hSh : ∀ j, shift.getD j 0 ≤ Sh) (hb : bound < 2 ^ 40)
    (hSh40 : Sh < 2 ^ 40) (hQ45 : Q < 2 ^ 45)
    (hSB : Sh + bound + 1 + 2 * (Q + bound + 2) ≤ SB) (h37 : 3 * (Q + bound + 2) ≤ 2 ^ 37) :
    machineCost P certifiedSolveC.costIdx [encodeValue equation, encodeValue shift,
        encodeValue bound] ≤
      certSolveCost p L Q w m (maxOrder (fullWindowExactNullspaceProblem FFT.fftModContext equation
        bound)) := by
  have hs' := hs
  obtain ⟨hw, hm, hw30, hm30, hQ, hmod, hred⟩ := hs'
  have hsW : equation.solutionWidth = w := hw
  have hmonic : ∀ j < equation.moduli.size, (equation.moduli.getD j 0).monic = true :=
    fun j hj ↦ (hmod j (by omega)).1
  obtain ⟨hpo, hprow, hpent, hpsize⟩ := liftProblem_sizes equation bound hmonic
  set prob := fullWindowExactNullspaceProblem FFT.fftModContext equation bound with hprob
  set eShift := certShift equation shift bound with heShift
  set o := maxOrder prob with ho
  have hord : ∀ x ∈ prob.orders.toList, x ≤ Q + bound + 2 := by
    intro x hx
    change x ∈ (equation.moduli.map fun M ↦ M.natDegree + bound + 2).toList at hx
    rw [Array.toList_map, List.mem_map] at hx
    obtain ⟨M, hM, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hM
    have hj' : j < m := by simpa [hm] using hj
    have hsz := (hmod j hj').2
    have hget : equation.moduli.getD j 0 = equation.moduli.toList[j] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj)]
      simp
    rw [hget] at hsz
    have := natDegree_le_size equation.moduli.toList[j]
    omega
  have hoQ : o ≤ Q + bound + 2 := maxOrder_lt prob _ hord
  have hq64 : ∀ b, (equation.moduli.getD b 0).val.size < 2 ^ 64 := by
    intro b
    rcases Nat.lt_or_ge b m with hb' | hb'
    · have := (hmod b hb').2; omega
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none,
        size_zero_val]
      norm_num
  have hsv : ∀ x ∈ shift.toList, x < 2 ^ 63 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have := hSh j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj)] at this
    simp only [Option.getD_some, Array.getElem_toList] at this ⊢
    omega
  have hg := certifiedGuardC_cost P (by includes) equation shift (by omega) (by omega) (by omega)
    (by omega) hMW hq64
  rw [certifiedSolveC.costEq P hP, ← hprob, ← heShift]
  unfold certSolveCost
  split
  · rename_i hguard
    rw [ModularEquation.solutionWidth.c548.costEq P (by includes),
      certShift.c568.costEq P (by includes)]
    have hsh := exactNullspaceShiftC_cost P (by includes) shift equation.moduli.size bound
      (by omega) hsv
    have hfw := fullWindowProblemC_cost P (by includes) equation bound (by omega) hs
    have hfuel := pmBasisFuelC_cost P (by includes) prob (fun x hx ↦ by have := hord x hx; omega)
    have heS : ∀ j, eShift.getD j 0 ≤ Sh + bound + 1 := certShift_getD_le equation shift bound hSh
    have hesz : eShift.size = prob.matrix.size := by
      rw [hpsize, heShift]
      simp [certShift, exactNullspaceShift, liftedPrincipalShift, hshift, hsW]
    have hsizeLe : PMCore.SizeLe prob.matrix (2 ^ 40) := by
      intro i j
      rw [Array.getD_eq_getD_getElem?]
      cases hi : prob.matrix[i]? with
      | none =>
        simp only [Option.getD_none]
        rw [rowGet_of_size_le (by simp), size_zero_val]
        norm_num
      | some row =>
        simp only [Option.getD_some]
        have hrow := Array.mem_toList_iff.2 (Array.mem_of_getElem? hi)
        rw [rowGet, Array.getD_eq_getD_getElem?]
        cases hj : row[j]? with
        | none => simp only [Option.getD_none, size_zero_val]; norm_num
        | some e =>
          have := hpent row hrow e (Array.mem_of_getElem? hj)
          simp only [Option.getD_some]
          omega
    have hinv : PMCore.CoreInv (w + m) m SB prob eShift :=
      ⟨by rw [hpsize, hsW, hm], fun row hr ↦ by rw [hprow row hr, hm], by rw [hpo, hm], hsizeLe,
        fun j ↦ by have := heS j; omega, by omega⟩
    have hcore' := hcore prob eShift hinv
    rw [← pmTreeEval_eq] at hcore'
    obtain ⟨hBsize, hBrows⟩ := certBasis_spec prob eShift
    set B := (popovEvalPMBasisContext FFT.novelTransform FFT.fftMulContext FFT.fftMulLowContext
      1).basis prob eShift with hBdef
    have hrw : ∀ row ∈ B.toList, RowWithin (w + m) (o + 2) row := by
      intro row hr
      obtain ⟨hsz, hd⟩ := hBrows row hr
      have := rowWithin_of_natDegree (C := w + m) (d := o + 1) (by omega)
        (fun j ↦ (hd j).trans (by omega))
      exact this
    have hl := fun row ↦ RunsApp.of_spec (us := [encodeValue bound,
      encodeValue (equation.solutionWidth + equation.moduli.size), encodeValue eShift])
      (vs := [encodeValue row])
      (certifiedSolveC.lam0.costSpec P (by includes) bound _ eShift row)
    have hfil := filter_cost P (by includes)
      (certifiedRow (equation.solutionWidth + equation.moduli.size) eShift bound)
      (.closure certifiedSolveC.lam0.costIdx [encodeValue bound,
        encodeValue (equation.solutionWidth + equation.moduli.size), encodeValue eShift]) hl
      (84 * (w + m) + 48) B.toList (fun row hr ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [certifiedSolveC.lam0.costEq P (by includes)]
        have := certifiedRowC_cost P (by includes) (C := w + m) (D := o + 2) (S := Sh + bound + 1)
          (by omega) (by omega) (equation.solutionWidth + equation.moduli.size) (by omega)
          eShift heS bound (by omega) row (hrw row hr)
        omega)
    have hpr := principalSolutionRowsC_cost P (by includes) equation.solutionWidth (by omega)
      (B.filter (certifiedRow (equation.solutionWidth + equation.moduli.size) eShift bound))
    have hfs : (B.filter (certifiedRow (equation.solutionWidth + equation.moduli.size) eShift
        bound)).size ≤ w + m := Array.size_filter_le.trans (by omega)
    have hfl : (B.toList.filter (certifiedRow (equation.solutionWidth + equation.moduli.size)
        eShift bound)).length ≤ w + m := (List.length_filter_le _ _).trans (by simp; omega)
    have hpr' := Nat.mul_le_mul_left (38 * equation.solutionWidth + 34) hfs
    simp only [Array.length_toList] at hfil
    rw [hBsize, hpsize] at hfil
    have hk : B.size = w + m := by rw [hBsize, hpsize, hsW, hm]
    rw [← ho] at hcore'
    rw [hsW] at hpr hpr'
    rw [hsW, hm] at hfil
    have e1 : (84 * (w + m) + 48 + 15) * (w + m) = (w + m) * (84 * (w + m) + 63) := by ring
    simp only [hsW, hm] at *
    cost_simp
    omega
  · omega

end

end LeanVM.Cost.Bounds.PMSolve
