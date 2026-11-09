module

-- CompPoly's completeness helpers (`me_*`) are private to its module: `import all` reads them.
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Completeness
public import LeanVM.Protocol.Extraction.Fast.WindowedSolve

/-!
# The certified solve without the modular filter

CompPoly's solver keeps the PM-basis rows whose principal part satisfies the modular equations
(`filterModularSolutionRows`), a test that multiplies each
candidate row by the relation matrix: at `(28, 4)` about `152 · 122 · 30 ≈ 2^19.1` univariate
products of degree up to `≈ 2^31`, a price of the order of the PM-basis's own, outside its model.

The test is not needed. The certified problem's orders are `deg M_b + W + 2`: a row of the lifted
problem of expanded shifted degree at most `2W + 1` has principal entries of shifted degree at most
`W` and quotient entries of degree at most `W + 1`, so its column products have degree below the
orders, and vanishing to the order is vanishing exactly. That is the second half of CompPoly's
`me_verification_dominates`, here a lemma of its own (**`certifiedRow_sound`**: such a basis row's
principal part is a nonzero modular solution of shifted degree at most the row's minus `W + 1`).
Its first half is the completeness (**`certifiedRow_complete`**): a solution of shifted degree
`e ≤ W` lifts to a lifted solution of expanded degree at most `e + W + 1`, so the basis has a row
of at most that degree.

`certifiedSolutionBasis` keeps the basis rows of expanded shifted degree at most `2W + 1` (a degree
read per row, no product), their principal parts; `certifiedModularSolutionBasisContext` is the
solver context on it, sound and complete-minimal.

Credits: the two halves are CompPoly's proof of `me_verification_dominates`
(`ModularEquation/Completeness.lean`, github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright
(c) 2026 CompPoly Contributors", Valerii Huhnin), split, the soundness half stated for any basis
row of expanded degree at most `2W + 1`, of any size.
-/

namespace LeanVM.Extraction.Fast

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- **The soundness half**: a basis row of the certified problem at `bound` of expanded shifted
degree `Db ≤ 2·bound + 1` has a principal part that is a nonzero modular solution, of shifted
degree at most `Db − (bound + 1)`. -/
theorem certifiedRow_sound (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (bound : Nat)
    (hmonic : ∀ b, b < equation.moduli.size → (equation.moduli.getD b 0).monic)
    (hcols : equation.moduli.size ≤ MatrixWidth equation.matrix)
    (hshift : shift.size = equation.solutionWidth) (hpos : 0 < equation.solutionWidth)
    {bRow : PolynomialRow F} {Db : Nat}
    (hbMem : bRow ∈ MatrixRows (pmCtx.basis (fullWindowExactNullspaceProblem modCtx equation bound)
      (exactNullspaceShift shift equation.moduli.size bound)))
    (hbDeg : rowShiftedDegree? bRow (exactNullspaceShift shift equation.moduli.size bound) =
      some Db)
    (hbSizeLe : bRow.size ≤ equation.solutionWidth + equation.moduli.size)
    (hDb2 : Db ≤ 2 * bound + 1) :
    rowSatisfiesModularBool mulCtx modCtx
        ((List.range equation.solutionWidth).map fun j ↦ rowGet bRow j).toArray
        equation.matrix equation.moduli = true ∧
      rowIsZero ((List.range equation.solutionWidth).map fun j ↦ rowGet bRow j).toArray = false ∧
      ∃ degB, rowShiftedDegree? ((List.range equation.solutionWidth).map
          fun j ↦ rowGet bRow j).toArray shift = some degB ∧ degB + bound + 1 ≤ Db := by
  classical
  set sW := equation.solutionWidth with hsWdef
  set mW := equation.moduli.size with hmWdef
  -- The reduced principal block and the lift matrix.
  set Fred : PolynomialMatrix F := ofFn sW mW
    (fun i j ↦ modByMonicWith modCtx (rowGet (equation.matrix.getD i #[]) j)
      (equation.moduli.getD j 0)) with hFred
  set liftM : PolynomialMatrix F := Fred ++ negativeDiagonalRows equation.moduli
    with hliftM
  have hFredSize : Fred.size = sW := ofFn_size _ _ _
  have hnegSize : (negativeDiagonalRows equation.moduli).size = mW := ofFn_size _ _ _
  have hliftSize : liftM.size = sW + mW := by
    rw [hliftM, Array.size_append, hFredSize, hnegSize]
  have hFredWidth : MatrixWidth Fred = mW := by
    rw [hFred, MatrixWidth_ofFn, ite_eq_right (by omega)]
  have hFredEntry : ∀ {k b : Nat}, k < sW → b < mW →
      rowGet (Fred.getD k #[]) b =
        modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
          (equation.moduli.getD b 0) := by
    intro k b hk hb
    rw [hFred, rowGet_ofFn, ite_eq_left ⟨hk, hb⟩]
  have hliftWidth : MatrixWidth liftM = mW := by
    rw [me_matrixWidth_eq_getD, hliftM, me_getD_append_left _ (by omega), hFred,
      getD_ofFn, ite_eq_left (by omega)]
    simp
  have hliftRows : ∀ r ∈ MatrixRows liftM, r.size = mW := by
    intro r hr
    rw [MatrixRows, hliftM, Array.toList_append, List.mem_append] at hr
    rcases hr with hr | hr
    · rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
      have hi' : i < Fred.size := by simpa using hi
      have hgetD : Fred.getD i #[] = r := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
        simpa [Array.getElem_toList] using hget
      rw [← hgetD, hFred, getD_ofFn, ite_eq_left (by omega)]
      simp
    · rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
      have hi' : i < (negativeDiagonalRows equation.moduli).size := by simpa using hi
      have hgetD : (negativeDiagonalRows equation.moduli).getD i #[] = r := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
        simpa [Array.getElem_toList] using hget
      rw [← hgetD, negativeDiagonalRows, getD_ofFn, ite_eq_left (by omega)]
      simp only [List.size_toArray, List.length_map, List.length_range]
      omega
  have hwf : WellFormed liftM := by
    intro r hr
    rw [hliftWidth]
    exact hliftRows r hr
  have hliftL : ∀ {k b : Nat}, k < sW → b < mW →
      rowGet (liftM.getD k #[]) b =
        modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
          (equation.moduli.getD b 0) := by
    intro k b hk hb
    rw [hliftM, me_getD_append_left _ (by omega)]
    exact hFredEntry hk hb
  have hliftR : ∀ {c b : Nat}, c < mW → b < mW →
      rowGet (liftM.getD (sW + c) #[]) b =
        (if c == b then -(equation.moduli.getD c 0) else 0) := by
    intro c b hc hb
    rw [hliftM, me_getD_append_right _ (by omega)]
    rw [show sW + c - Fred.size = c from by omega]
    rw [negativeDiagonalRows, rowGet_ofFn, ite_eq_left ⟨by omega, by omega⟩]
  -- Monicity facts.
  have hMon : ∀ {b : Nat}, b < mW →
      Polynomial.Monic ((equation.moduli.getD b 0).toPoly) :=
    fun {b} hb ↦ (CPolynomial.monic_toPoly_iff _).mp (hmonic b hb)
  have hMne : ∀ {b : Nat}, b < mW → ((equation.moduli.getD b 0).toPoly) ≠ 0 :=
    fun {b} hb ↦ (hMon hb).ne_zero
  -- The verification problem and shift.
  set P := fullWindowExactNullspaceProblem modCtx equation bound with hP
  have hPmatrix : P.matrix = liftM := rfl
  have hPordersSize : P.orders.size = mW := by
    rw [hP, fullWindowExactNullspaceProblem]
    simp only [Array.size_map]
    omega
  have hPorders : ∀ {b : Nat}, b < mW →
      P.orders.getD b 0 = (equation.moduli.getD b 0).natDegree + bound + 2 := by
    intro b hb
    show (equation.moduli.map fun m ↦ m.natDegree + bound + 2).getD b 0 = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
      Option.getD_some]
  set eShift := exactNullspaceShift shift equation.moduli.size bound with heShift
  have heShiftL : ∀ {k : Nat}, k < sW →
      eShift.getD k 0 = shift.getD k 0 + bound + 1 := by
    intro k hk
    rw [heShift, exactNullspaceShift, liftedPrincipalShift, principalShiftOffset,
      me_getD_append_left _ (by simp [hshift]; omega)]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_getElem (by omega : k < shift.size), Option.map_some,
      Option.getD_some, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega : k < shift.size), Option.getD_some]
    omega
  have heShiftR : ∀ {c : Nat}, c < mW →
      eShift.getD (sW + c) 0 = bound := by
    intro c hc
    rw [heShift, exactNullspaceShift, quotientShift,
      me_getD_append_right _ (by simp [liftedPrincipalShift, hshift])]
    rw [show sW + c - (liftedPrincipalShift shift bound).size = c from by
      simp [liftedPrincipalShift, hshift]]
    exact me_getD_replicate _ _ hc
  have hFredZero : ∀ {k b : Nat}, k < sW → b < mW →
      (equation.moduli.getD b 0).natDegree = 0 →
      (rowGet (Fred.getD k #[]) b).toPoly = 0 := by
    intro k b hk hb hMdeg
    rw [hFredEntry hk hb, me_modByMonicWith_toPoly modCtx (hMon hb)]
    have hMone : (equation.moduli.getD b 0).toPoly = 1 := by
      refine (Polynomial.Monic.natDegree_eq_zero (hMon hb)).mp ?_
      rwa [CPolynomial.natDegree_toPoly] at hMdeg
    rw [hMone, Polynomial.modByMonic_one]
  have hFredDegLt : ∀ {k b : Nat}, k < sW → b < mW →
      (rowGet (Fred.getD k #[]) b).toPoly ≠ 0 →
      (rowGet (Fred.getD k #[]) b).toPoly.natDegree <
        (equation.moduli.getD b 0).natDegree := by
    intro k b hk hb hne
    rw [hFredEntry hk hb, me_modByMonicWith_toPoly modCtx (hMon hb)] at hne ⊢
    rw [CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_lt_natDegree hne
      (Polynomial.degree_modByMonic_lt _ (hMon hb))
  set e := Db - (bound + 1) with he
  have hDb : Db ≤ e + bound + 1 := by omega
  have hebound : e ≤ bound := by omega
  -- Entry bounds on the dominated basis row.
  have hbEntryL : ∀ {k : Nat}, k < sW → rowGet bRow k ≠ 0 →
      (rowGet bRow k).toPoly.natDegree + shift.getD k 0 ≤ e := by
    intro k hk hne
    have h := me_entry_le_of_rowShiftedDegree hbDeg hne
    rw [heShiftL hk] at h
    rw [CPolynomial.natDegree_toPoly] at h
    omega
  have hbEntryR : ∀ {c : Nat}, c < mW → rowGet bRow (sW + c) ≠ 0 →
      (rowGet bRow (sW + c)).toPoly.natDegree ≤ e + 1 := by
    intro c hc hne
    have h := me_entry_le_of_rowShiftedDegree hbDeg hne
    rw [heShiftR hc] at h
    rw [CPolynomial.natDegree_toPoly] at h
    omega
  -- The verification orders force exact column products for the basis row.
  have hsound := pmCtx.sound P eShift bRow hbMem
  have hTzero : ∀ {j : Nat}, j < mW →
      ∑ k ∈ Finset.range (sW + mW), (rowGet bRow k).toPoly *
        (rowGet (liftM.getD k #[]) j).toPoly = 0 := by
    intro j hjm
    have hX := hsound j (by omega)
    rw [truncateX_eq_zero_iff_X_pow_dvd] at hX
    rw [hPmatrix] at hX
    rw [me_rowMul_toPoly pmCtx.runtime.mulContext bRow liftM (by omega)
      hbSizeLe] at hX
    rw [hPorders hjm] at hX
    refine me_eq_zero_of_X_pow_dvd_of_natDegree_lt hX ?_
    have hdegT : (∑ k ∈ Finset.range (sW + mW), (rowGet bRow k).toPoly *
        (rowGet (liftM.getD k #[]) j).toPoly).natDegree ≤
        (equation.moduli.getD j 0).natDegree + bound + 1 := by
      refine me_natDegree_sum_le _ fun k hk ↦ ?_
      by_cases hz : (rowGet bRow k).toPoly = 0
      · rw [hz, zero_mul, Polynomial.natDegree_zero]
        exact Nat.zero_le _
      have hne : rowGet bRow k ≠ 0 :=
        fun h ↦ hz (by rw [h, CPolynomial.toPoly_zero])
      rcases Nat.lt_or_ge k sW with hkL | hkR
      · by_cases hzF : (rowGet (liftM.getD k #[]) j).toPoly = 0
        · rw [hzF, mul_zero, Polynomial.natDegree_zero]
          exact Nat.zero_le _
        · have hzF' : (rowGet (Fred.getD k #[]) j).toPoly ≠ 0 := by
            rwa [hliftM, me_getD_append_left _ (by omega)] at hzF
          have hMdeg1 : 1 ≤ (equation.moduli.getD j 0).natDegree := by
            by_contra hcon
            exact hzF' (hFredZero hkL hjm (by omega))
          have hFle := hFredDegLt hkL hjm hzF'
          have ha := hbEntryL hkL hne
          have hentry : rowGet (liftM.getD k #[]) j = rowGet (Fred.getD k #[]) j := by
            rw [hliftM, me_getD_append_left _ (by omega)]
          rw [hentry]
          refine le_trans Polynomial.natDegree_mul_le ?_
          omega
      · have hcm : k - sW < mW := by omega
        rw [show k = sW + (k - sW) from by omega, hliftR hcm hjm]
        by_cases hcj : k - sW = j
        · rw [ite_eq_left (by simpa using hcj)]
          have hb1 : (rowGet bRow (sW + j)).toPoly.natDegree ≤ e + 1 := by
            refine hbEntryR hjm ?_
            rwa [show sW + j = k from by omega]
          refine le_trans Polynomial.natDegree_mul_le ?_
          rw [hcj, CPolynomial.toPoly_neg, Polynomial.natDegree_neg,
            ← CPolynomial.natDegree_toPoly (equation.moduli.getD j 0)]
          omega
        · rw [ite_eq_right (by simpa using hcj), CPolynomial.toPoly_zero, mul_zero,
            Polynomial.natDegree_zero]
          exact Nat.zero_le _
    omega
  have hbProd : ∀ {j : Nat}, j < mW →
      ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
        (rowGet (Fred.getD k #[]) j).toPoly =
      (rowGet bRow (sW + j)).toPoly * (equation.moduli.getD j 0).toPoly := by
    intro j hjm
    have h0 := hTzero hjm
    rw [me_sum_range_add (fun k ↦ (rowGet bRow k).toPoly *
      (rowGet (liftM.getD k #[]) j).toPoly) sW mW] at h0
    have hfirst : ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
        (rowGet (liftM.getD k #[]) j).toPoly =
        ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (Fred.getD k #[]) j).toPoly := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' : k < sW := Finset.mem_range.mp hk
      rw [hliftM, me_getD_append_left _ (by omega)]
    have hsecond : ∑ k ∈ Finset.range mW, (rowGet bRow (sW + k)).toPoly *
        (rowGet (liftM.getD (sW + k) #[]) j).toPoly =
        -((rowGet bRow (sW + j)).toPoly * (equation.moduli.getD j 0).toPoly) := by
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjm) ?_]
      · rw [hliftR hjm hjm, ite_eq_left (by simp), CPolynomial.toPoly_neg]
        ring
      · intro c hc hcj
        rw [hliftR (Finset.mem_range.mp hc) hjm, ite_eq_right (by simpa using hcj),
          CPolynomial.toPoly_zero, mul_zero]
    rw [hfirst, hsecond] at h0
    have h0' : ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
        (rowGet (Fred.getD k #[]) j).toPoly -
        (rowGet bRow (sW + j)).toPoly * (equation.moduli.getD j 0).toPoly = 0 := by
      rw [sub_eq_add_neg]
      exact h0
    exact sub_eq_zero.mp h0'
  -- The principal truncation of the basis row.
  set bPrin : PolynomialRow F :=
    ((List.range sW).map fun j ↦ rowGet bRow j).toArray with hbPrin
  have hbPrinSize : bPrin.size = sW := by simp [hbPrin]
  have hbPrinGet : ∀ k, rowGet bPrin k = if k < sW then rowGet bRow k else 0 := by
    intro k
    rw [hbPrin, rowGet, me_getD_list_range_map]
  have hbDvdF : ∀ {j : Nat}, j < mW → (equation.moduli.getD j 0).toPoly ∣
      ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
        (rowGet (equation.matrix.getD k #[]) j).toPoly := by
    intro j hjm
    have hsumdvd : (equation.moduli.getD j 0).toPoly ∣
        ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (Fred.getD k #[]) j).toPoly := by
      rw [hbProd hjm]
      exact dvd_mul_left _ _
    have hdiff : (equation.moduli.getD j 0).toPoly ∣
        (∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (Fred.getD k #[]) j).toPoly) -
        ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (equation.matrix.getD k #[]) j).toPoly := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun k hk ↦ ?_
      rw [hFredEntry (Finset.mem_range.mp hk) hjm]
      have hsub := me_dvd_modByMonicWith_sub modCtx
        (p := rowGet (equation.matrix.getD k #[]) j) (hMon hjm)
      have hfac : (rowGet bRow k).toPoly *
          (modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) j)
            (equation.moduli.getD j 0)).toPoly -
          (rowGet bRow k).toPoly *
            (rowGet (equation.matrix.getD k #[]) j).toPoly =
          (rowGet bRow k).toPoly *
            ((modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) j)
              (equation.moduli.getD j 0)).toPoly -
              (rowGet (equation.matrix.getD k #[]) j).toPoly) := by
        ring
      rw [hfac]
      exact Dvd.dvd.mul_left hsub _
    have h := dvd_sub hsumdvd hdiff
    simpa using h
  have hbPrinSat : rowSatisfiesModularBool mulCtx modCtx bPrin equation.matrix
      equation.moduli = true := by
    rw [me_rowSatisfies_iff]
    intro b hb
    rw [me_modByMonicWith_eq_zero_iff_dvd modCtx (hMon hb)]
    rw [me_rowMul_toPoly mulCtx bPrin equation.matrix (lt_of_lt_of_le hb hcols)
      (le_of_eq hbPrinSize)]
    have hcong : ∑ k ∈ Finset.range sW, (rowGet bPrin k).toPoly *
        (rowGet (equation.matrix.getD k #[]) b).toPoly =
        ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (equation.matrix.getD k #[]) b).toPoly := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hbPrinGet, ite_eq_left (Finset.mem_range.mp hk)]
    rw [hcong]
    exact hbDvdF hb
  have hbPrinNz : rowIsZero bPrin = false := by
    cases hzero : rowIsZero bPrin with
    | false => rfl
    | true =>
        exfalso
        have hallP : ∀ k, k < sW → rowGet bRow k = 0 := by
          intro k hk
          have h := me_rowGet_eq_zero_of_rowIsZero hzero k
          rwa [hbPrinGet, ite_eq_left hk] at h
        have hallQ : ∀ c, c < mW → rowGet bRow (sW + c) = 0 := by
          intro c hc
          have hprod := hbProd hc
          have hzeroSum : ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
              (rowGet (Fred.getD k #[]) c).toPoly = 0 :=
            Finset.sum_eq_zero fun k hk ↦ by
              rw [hallP k (Finset.mem_range.mp hk), CPolynomial.toPoly_zero,
                zero_mul]
          rw [hzeroSum] at hprod
          rcases mul_eq_zero.mp hprod.symm with h | h
          · exact (CPolynomial.toPoly_eq_zero_iff _).mp h
          · exact absurd h (hMne hc)
        have hzRow : RowIsZero bRow := by
          refine me_rowIsZero_of_forall fun k hk ↦ ?_
          rcases Nat.lt_or_ge k sW with h1 | h1
          · exact hallP k h1
          · have hcm : k - sW < mW := by omega
            rw [show k = sW + (k - sW) from by omega]
            exact hallQ _ hcm
        have hnone := (rowShiftedDegree?_eq_none_iff
          (row := bRow) (shift := eShift)).mpr hzRow
        rw [hbDeg] at hnone
        cases hnone
  obtain ⟨degB, hdegB⟩ := me_rowShiftedDegree_isSome (shift := shift) hbPrinNz
  refine ⟨hbPrinSat, hbPrinNz, degB, hdegB, ?_⟩
  obtain ⟨j, hjsize, hjne, hjeq⟩ := me_rowShiftedDegree_attained hdegB
  rw [hbPrinSize] at hjsize
  have hjne' : rowGet bRow j ≠ 0 := by rwa [hbPrinGet, ite_eq_left hjsize] at hjne
  have h := me_entry_le_of_rowShiftedDegree hbDeg hjne'
  rw [heShiftL hjsize] at h
  rw [hbPrinGet, ite_eq_left hjsize] at hjeq
  omega

/-- **The completeness half**: a nonzero in-width solution of shifted degree `e ≤ bound` lifts, so
the certified problem's basis has a row of expanded shifted degree at most `e + bound + 1`. -/
theorem certifiedRow_complete (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (bound : Nat) {rowStar : PolynomialRow F} {e : Nat}
    (hmonic : ∀ b, b < equation.moduli.size → (equation.moduli.getD b 0).monic)
    (hcols : equation.moduli.size ≤ MatrixWidth equation.matrix)
    (hshift : shift.size = equation.solutionWidth)
    (hpos : 0 < equation.solutionWidth)
    (hsat : rowSatisfiesModularBool mulCtx modCtx rowStar equation.matrix
      equation.moduli = true)
    (hnz : rowIsZero rowStar = false)
    (hwidth : rowStar.size ≤ equation.solutionWidth)
    (hdeg : rowShiftedDegree? rowStar shift = some e) :
    ∃ bRow Db,
      bRow ∈ MatrixRows (pmCtx.basis (fullWindowExactNullspaceProblem modCtx equation bound)
        (exactNullspaceShift shift equation.moduli.size bound)) ∧
      bRow.size ≤ equation.solutionWidth + equation.moduli.size ∧
      rowShiftedDegree? bRow (exactNullspaceShift shift equation.moduli.size bound) = some Db ∧
      Db ≤ e + bound + 1 := by
  classical
  set sW := equation.solutionWidth with hsWdef
  set mW := equation.moduli.size with hmWdef
  -- The reduced principal block and the lift matrix.
  set Fred : PolynomialMatrix F := ofFn sW mW
    (fun i j ↦ modByMonicWith modCtx (rowGet (equation.matrix.getD i #[]) j)
      (equation.moduli.getD j 0)) with hFred
  set liftM : PolynomialMatrix F := Fred ++ negativeDiagonalRows equation.moduli
    with hliftM
  have hFredSize : Fred.size = sW := ofFn_size _ _ _
  have hnegSize : (negativeDiagonalRows equation.moduli).size = mW := ofFn_size _ _ _
  have hliftSize : liftM.size = sW + mW := by
    rw [hliftM, Array.size_append, hFredSize, hnegSize]
  have hFredWidth : MatrixWidth Fred = mW := by
    rw [hFred, MatrixWidth_ofFn, ite_eq_right (by omega)]
  have hFredEntry : ∀ {k b : Nat}, k < sW → b < mW →
      rowGet (Fred.getD k #[]) b =
        modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
          (equation.moduli.getD b 0) := by
    intro k b hk hb
    rw [hFred, rowGet_ofFn, ite_eq_left ⟨hk, hb⟩]
  have hliftWidth : MatrixWidth liftM = mW := by
    rw [me_matrixWidth_eq_getD, hliftM, me_getD_append_left _ (by omega), hFred,
      getD_ofFn, ite_eq_left (by omega)]
    simp
  have hliftRows : ∀ r ∈ MatrixRows liftM, r.size = mW := by
    intro r hr
    rw [MatrixRows, hliftM, Array.toList_append, List.mem_append] at hr
    rcases hr with hr | hr
    · rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
      have hi' : i < Fred.size := by simpa using hi
      have hgetD : Fred.getD i #[] = r := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
        simpa [Array.getElem_toList] using hget
      rw [← hgetD, hFred, getD_ofFn, ite_eq_left (by omega)]
      simp
    · rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
      have hi' : i < (negativeDiagonalRows equation.moduli).size := by simpa using hi
      have hgetD : (negativeDiagonalRows equation.moduli).getD i #[] = r := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
        simpa [Array.getElem_toList] using hget
      rw [← hgetD, negativeDiagonalRows, getD_ofFn, ite_eq_left (by omega)]
      simp only [List.size_toArray, List.length_map, List.length_range]
      omega
  have hwf : WellFormed liftM := by
    intro r hr
    rw [hliftWidth]
    exact hliftRows r hr
  have hliftL : ∀ {k b : Nat}, k < sW → b < mW →
      rowGet (liftM.getD k #[]) b =
        modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
          (equation.moduli.getD b 0) := by
    intro k b hk hb
    rw [hliftM, me_getD_append_left _ (by omega)]
    exact hFredEntry hk hb
  have hliftR : ∀ {c b : Nat}, c < mW → b < mW →
      rowGet (liftM.getD (sW + c) #[]) b =
        (if c == b then -(equation.moduli.getD c 0) else 0) := by
    intro c b hc hb
    rw [hliftM, me_getD_append_right _ (by omega)]
    rw [show sW + c - Fred.size = c from by omega]
    rw [negativeDiagonalRows, rowGet_ofFn, ite_eq_left ⟨by omega, by omega⟩]
  -- Monicity facts.
  have hMon : ∀ {b : Nat}, b < mW →
      Polynomial.Monic ((equation.moduli.getD b 0).toPoly) :=
    fun {b} hb ↦ (CPolynomial.monic_toPoly_iff _).mp (hmonic b hb)
  have hMne : ∀ {b : Nat}, b < mW → ((equation.moduli.getD b 0).toPoly) ≠ 0 :=
    fun {b} hb ↦ (hMon hb).ne_zero
  -- The verification problem and shift.
  set P := fullWindowExactNullspaceProblem modCtx equation bound with hP
  have hPmatrix : P.matrix = liftM := rfl
  have hPordersSize : P.orders.size = mW := by
    rw [hP, fullWindowExactNullspaceProblem]
    simp only [Array.size_map]
    omega
  have hPorders : ∀ {b : Nat}, b < mW →
      P.orders.getD b 0 = (equation.moduli.getD b 0).natDegree + bound + 2 := by
    intro b hb
    show (equation.moduli.map fun m ↦ m.natDegree + bound + 2).getD b 0 = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
      Option.getD_some]
  set eShift := exactNullspaceShift shift equation.moduli.size bound with heShift
  have heShiftL : ∀ {k : Nat}, k < sW →
      eShift.getD k 0 = shift.getD k 0 + bound + 1 := by
    intro k hk
    rw [heShift, exactNullspaceShift, liftedPrincipalShift, principalShiftOffset,
      me_getD_append_left _ (by simp [hshift]; omega)]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_getElem (by omega : k < shift.size), Option.map_some,
      Option.getD_some, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega : k < shift.size), Option.getD_some]
    omega
  have heShiftR : ∀ {c : Nat}, c < mW →
      eShift.getD (sW + c) 0 = bound := by
    intro c hc
    rw [heShift, exactNullspaceShift, quotientShift,
      me_getD_append_right _ (by simp [liftedPrincipalShift, hshift])]
    rw [show sW + c - (liftedPrincipalShift shift bound).size = c from by
      simp [liftedPrincipalShift, hshift]]
    exact me_getD_replicate _ _ hc
  -- Divisibility of the original products.
  have hdvdF : ∀ {b : Nat}, b < mW →
      (equation.moduli.getD b 0).toPoly ∣
        ∑ k ∈ Finset.range sW, (rowGet rowStar k).toPoly *
          (rowGet (equation.matrix.getD k #[]) b).toPoly := by
    intro b hb
    have hsat' := (me_rowSatisfies_iff mulCtx modCtx rowStar equation.matrix
      equation.moduli).mp hsat b hb
    have hdvd := (me_modByMonicWith_eq_zero_iff_dvd modCtx (hMon hb)).mp hsat'
    rwa [me_rowMul_toPoly mulCtx rowStar equation.matrix
      (lt_of_lt_of_le hb hcols) hwidth] at hdvd
  -- The reduced products and their exact quotients.
  set prodE := fun b ↦ rowGet (rowMulMatrixWith mulCtx rowStar Fred) b with hprodE
  have hprodE_toPoly : ∀ {b : Nat}, b < mW →
      (prodE b).toPoly = ∑ k ∈ Finset.range sW, (rowGet rowStar k).toPoly *
        (rowGet (Fred.getD k #[]) b).toPoly := by
    intro b hb
    rw [hprodE]
    exact me_rowMul_toPoly mulCtx rowStar Fred (by omega) hwidth
  have hdvdRed : ∀ {b : Nat}, b < mW →
      (equation.moduli.getD b 0).toPoly ∣ (prodE b).toPoly := by
    intro b hb
    have hdiff : (equation.moduli.getD b 0).toPoly ∣
        (prodE b).toPoly -
          ∑ k ∈ Finset.range sW, (rowGet rowStar k).toPoly *
            (rowGet (equation.matrix.getD k #[]) b).toPoly := by
      rw [hprodE_toPoly hb, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun k hk ↦ ?_
      have hk' : k < sW := Finset.mem_range.mp hk
      rw [hFredEntry hk' hb]
      have hsub := me_dvd_modByMonicWith_sub modCtx
        (p := rowGet (equation.matrix.getD k #[]) b) (hMon hb)
      have hfac : (rowGet rowStar k).toPoly *
          (modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
            (equation.moduli.getD b 0)).toPoly -
          (rowGet rowStar k).toPoly *
            (rowGet (equation.matrix.getD k #[]) b).toPoly =
          (rowGet rowStar k).toPoly *
            ((modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
              (equation.moduli.getD b 0)).toPoly -
              (rowGet (equation.matrix.getD k #[]) b).toPoly) := by
        ring
      rw [hfac]
      exact Dvd.dvd.mul_left hsub _
    have hsum := dvd_add hdiff (hdvdF hb)
    simpa using hsum
  obtain ⟨quot, hquot⟩ : ∃ q : Nat → CPolynomial F,
      ∀ b, q b = (prodE b).divByMonic (equation.moduli.getD b 0) :=
    ⟨fun b ↦ (prodE b).divByMonic (equation.moduli.getD b 0), fun _ ↦ rfl⟩
  have hquotExact : ∀ {b : Nat}, b < mW →
      (quot b).toPoly * (equation.moduli.getD b 0).toPoly = (prodE b).toPoly := by
    intro b hb
    rw [hquot b, me_divByMonic_mul_eq (hmonic b hb) (hdvdRed hb)]
  -- Degree bounds on the witness entries and quotients.
  have hrowStarEntry : ∀ {k : Nat}, rowGet rowStar k ≠ 0 →
      (rowGet rowStar k).toPoly.natDegree + shift.getD k 0 ≤ e := by
    intro k hk
    have h := me_entry_le_of_rowShiftedDegree hdeg hk
    rwa [CPolynomial.natDegree_toPoly] at h
  have hFredZero : ∀ {k b : Nat}, k < sW → b < mW →
      (equation.moduli.getD b 0).natDegree = 0 →
      (rowGet (Fred.getD k #[]) b).toPoly = 0 := by
    intro k b hk hb hMdeg
    rw [hFredEntry hk hb, me_modByMonicWith_toPoly modCtx (hMon hb)]
    have hMone : (equation.moduli.getD b 0).toPoly = 1 := by
      refine (Polynomial.Monic.natDegree_eq_zero (hMon hb)).mp ?_
      rwa [CPolynomial.natDegree_toPoly] at hMdeg
    rw [hMone, Polynomial.modByMonic_one]
  have hFredDegLt : ∀ {k b : Nat}, k < sW → b < mW →
      (rowGet (Fred.getD k #[]) b).toPoly ≠ 0 →
      (rowGet (Fred.getD k #[]) b).toPoly.natDegree <
        (equation.moduli.getD b 0).natDegree := by
    intro k b hk hb hne
    rw [hFredEntry hk hb, me_modByMonicWith_toPoly modCtx (hMon hb)] at hne ⊢
    rw [CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_lt_natDegree hne
      (Polynomial.degree_modByMonic_lt _ (hMon hb))
  have hquotDeg : ∀ {b : Nat}, b < mW → quot b ≠ 0 →
      (quot b).toPoly.natDegree ≤ e := by
    intro b hb hqz
    have hqpoly : (quot b).toPoly ≠ 0 :=
      fun h ↦ hqz ((CPolynomial.toPoly_eq_zero_iff _).mp h)
    by_cases hMdeg : (equation.moduli.getD b 0).natDegree = 0
    · exfalso
      have hzero : (prodE b).toPoly = 0 := by
        rw [hprodE_toPoly hb]
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        rw [hFredZero (Finset.mem_range.mp hk) hb hMdeg, mul_zero]
      have hmul := hquotExact hb
      rw [hzero] at hmul
      rcases mul_eq_zero.mp hmul with h | h
      · exact hqpoly h
      · exact hMne hb h
    · have h2 : (prodE b).toPoly.natDegree =
          (quot b).toPoly.natDegree + (equation.moduli.getD b 0).natDegree := by
        rw [← hquotExact hb, CPolynomial.natDegree_toPoly (equation.moduli.getD b 0)]
        exact Polynomial.natDegree_mul hqpoly (hMne hb)
      have h1 : (prodE b).toPoly.natDegree ≤
          e + (equation.moduli.getD b 0).natDegree - 1 := by
        rw [hprodE_toPoly hb]
        refine me_natDegree_sum_le _ fun k hk ↦ ?_
        by_cases hz : (rowGet rowStar k).toPoly = 0
        · rw [hz, zero_mul, Polynomial.natDegree_zero]
          exact Nat.zero_le _
        by_cases hzF : (rowGet (Fred.getD k #[]) b).toPoly = 0
        · rw [hzF, mul_zero, Polynomial.natDegree_zero]
          exact Nat.zero_le _
        · have hne : rowGet rowStar k ≠ 0 :=
            fun h ↦ hz (by rw [h, CPolynomial.toPoly_zero])
          have ha := hrowStarEntry hne
          have hbnd := hFredDegLt hk hb hzF
          refine le_trans Polynomial.natDegree_mul_le ?_
          omega
      omega
  -- The lifted exact-nullspace row.
  set lifted : PolynomialRow F := ((List.range (sW + mW)).map
    (fun k ↦ if k < sW then rowGet rowStar k else quot (k - sW))).toArray
    with hlifted
  have hliftedSize : lifted.size = sW + mW := by simp [hlifted]
  have hliftedGet : ∀ k, rowGet lifted k =
      if k < sW + mW then (if k < sW then rowGet rowStar k else quot (k - sW))
      else 0 := by
    intro k
    rw [hlifted, rowGet, me_getD_list_range_map]
  have hliftedL : ∀ {k : Nat}, k < sW → rowGet lifted k = rowGet rowStar k := by
    intro k hk
    rw [hliftedGet, ite_eq_left (by omega), ite_eq_left hk]
  have hliftedR : ∀ {c : Nat}, c < mW → rowGet lifted (sW + c) = quot c := by
    intro c hc
    rw [hliftedGet, ite_eq_left (by omega), ite_eq_right (by omega)]
    rw [show sW + c - sW = c from by omega]
  obtain ⟨j0, hj0, hj0ne⟩ := exists_nonzero_entry_of_rowIsZero_false hnz
  have hj0sW : j0 < sW := by omega
  have hnzL : rowIsZero lifted = false := by
    refine me_rowIsZero_false_of_entry (j := j0) (by omega) ?_
    rw [hliftedL hj0sW]
    exact hj0ne
  -- The lifted row is an exact solution of the verification problem.
  have happroxL : ∀ j, j < P.orders.size →
      truncateX (P.orders.getD j 0)
        (rowGet (rowMulMatrixWith pmCtx.runtime.mulContext lifted P.matrix) j) = 0 := by
    intro j hj
    have hjm : j < mW := by omega
    have hzero : rowGet (rowMulMatrixWith pmCtx.runtime.mulContext lifted
        P.matrix) j = 0 := by
      refine (CPolynomial.toPoly_eq_zero_iff _).mp ?_
      rw [hPmatrix]
      rw [me_rowMul_toPoly pmCtx.runtime.mulContext lifted liftM (by omega)
        (le_of_eq hliftedSize)]
      rw [me_sum_range_add (fun k ↦ (rowGet lifted k).toPoly *
        (rowGet (liftM.getD k #[]) j).toPoly) sW mW]
      have hfirst : ∑ k ∈ Finset.range sW, (rowGet lifted k).toPoly *
          (rowGet (liftM.getD k #[]) j).toPoly = (prodE j).toPoly := by
        rw [hprodE_toPoly hjm]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk' : k < sW := Finset.mem_range.mp hk
        rw [hliftedL hk', hliftM, me_getD_append_left _ (by omega)]
      have hsecond : ∑ k ∈ Finset.range mW, (rowGet lifted (sW + k)).toPoly *
          (rowGet (liftM.getD (sW + k) #[]) j).toPoly =
          -((quot j).toPoly * (equation.moduli.getD j 0).toPoly) := by
        rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjm) ?_]
        · rw [hliftedR hjm, hliftR hjm hjm, ite_eq_left (by simp),
            CPolynomial.toPoly_neg]
          ring
        · intro c hc hcj
          rw [hliftR (Finset.mem_range.mp hc) hjm, ite_eq_right (by simpa using hcj),
            CPolynomial.toPoly_zero, mul_zero]
      rw [hfirst, hsecond, hquotExact hjm]
      ring
    rw [hzero]
    exact truncateX_zero _
  -- Apply the PM-basis minimality contract to the lifted row.
  obtain ⟨bRow, Db, hbMem, hbSize, hbDeg, hbDom⟩ :=
    pmCtx.complete_minimal P eShift lifted (by rw [hPmatrix]; omega)
      (by rw [hPmatrix]; exact hwf) happroxL hnzL
      (by rw [hPmatrix]; omega)
  have hbSizeLe : bRow.size ≤ sW + mW := by
    rw [hPmatrix, hliftSize] at hbSize
    exact hbSize
  -- The lifted row stays inside the expanded window.
  obtain ⟨Dl, hDl⟩ := me_rowShiftedDegree_isSome (shift := eShift) hnzL
  have hDlle : Dl ≤ e + bound + 1 := by
    obtain ⟨j, hjsize, hjne, hjeq⟩ := me_rowShiftedDegree_attained hDl
    rw [hliftedSize] at hjsize
    rcases Nat.lt_or_ge j sW with hjL | hjR
    · rw [heShiftL hjL, hliftedL hjL] at hjeq
      have hne' : rowGet rowStar j ≠ 0 := by rwa [hliftedL hjL] at hjne
      have h := me_entry_le_of_rowShiftedDegree hdeg hne'
      rw [CPolynomial.natDegree_toPoly] at h
      rw [CPolynomial.natDegree_toPoly] at hjeq
      omega
    · have hcm : j - sW < mW := by omega
      rw [show j = sW + (j - sW) from by omega] at hjne hjeq
      rw [hliftedR hcm] at hjne hjeq
      rw [heShiftR hcm] at hjeq
      have hqd := hquotDeg hcm hjne
      rw [CPolynomial.natDegree_toPoly] at hjeq
      omega
  have hDb : Db ≤ e + bound + 1 := le_trans (hbDom Dl hDl) hDlle
  exact ⟨bRow, Db, hbMem, hbSizeLe, hbDeg, hDb⟩


/-! ## The certified solve -/

/-- The expanded shift of the certified problem at the window `bound`. -/
@[expose] def certShift (equation : ModularEquation F) (shift : Array Nat) (bound : Nat) :
    Array Nat :=
  exactNullspaceShift shift equation.moduli.size bound

/-- Whether a lifted row is certified: at most `width` entries, expanded shifted degree at most
`2·bound + 1`. -/
@[expose] def certifiedRow (width : Nat) (eShift : Array Nat) (bound : Nat)
    (row : PolynomialRow F) : Bool :=
  decide (row.size ≤ width) &&
    match rowShiftedDegree? row eShift with
    | some D => decide (D ≤ 2 * bound + 1)
    | none => false

/-- The hypotheses of the certified rows' soundness, checked: a principal coordinate, the shift
aligned, every modular column in the relation matrix, the moduli monic. -/
@[expose] def certifiedGuard (equation : ModularEquation F) (shift : Array Nat) : Bool :=
  decide (0 < equation.solutionWidth) && decide (shift.size = equation.solutionWidth) &&
    decide (equation.moduli.size ≤ MatrixWidth equation.matrix) &&
    (List.range equation.moduli.size).all fun b ↦ (equation.moduli.getD b 0).monic

/-- **The certified solve**: the PM-basis of the certified problem at `bound`, its certified rows
(`certifiedRow`: a size and a degree read, no product), their principal parts. -/
@[expose] def certifiedSolutionBasis (modCtx : CPolynomial.ModContext F) (pmCtx : PMBasisContext F)
    (equation : ModularEquation F) (shift : Array Nat) (bound : Nat) : PolynomialMatrix F :=
  if certifiedGuard equation shift then
    principalSolutionRows equation.solutionWidth
      ((pmCtx.basis (fullWindowExactNullspaceProblem modCtx equation bound)
          (certShift equation shift bound)).filter
        (certifiedRow (equation.solutionWidth + equation.moduli.size)
          (certShift equation shift bound) bound))
  else #[]

omit [LawfulBEq F] in
theorem certifiedGuard_iff {equation : ModularEquation F} {shift : Array Nat} :
    certifiedGuard equation shift = true ↔
      0 < equation.solutionWidth ∧ shift.size = equation.solutionWidth ∧
        equation.moduli.size ≤ MatrixWidth equation.matrix ∧
        ∀ b, b < equation.moduli.size → (equation.moduli.getD b 0).monic := by
  simp only [certifiedGuard, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc]

omit [LawfulBEq F] in
theorem certifiedRow_iff {width : Nat} {eShift : Array Nat} {bound : Nat} {row : PolynomialRow F} :
    certifiedRow width eShift bound row = true ↔
      row.size ≤ width ∧ ∃ D, rowShiftedDegree? row eShift = some D ∧ D ≤ 2 * bound + 1 := by
  unfold certifiedRow
  cases rowShiftedDegree? row eShift <;> simp

theorem mem_certifiedSolutionBasis {modCtx : CPolynomial.ModContext F} {pmCtx : PMBasisContext F}
    {equation : ModularEquation F} {shift : Array Nat} {bound : Nat} {row : PolynomialRow F} :
    row ∈ MatrixRows (certifiedSolutionBasis modCtx pmCtx equation shift bound) ↔
      certifiedGuard equation shift = true ∧
      ∃ bRow, bRow ∈ MatrixRows (pmCtx.basis (fullWindowExactNullspaceProblem modCtx equation bound)
          (certShift equation shift bound)) ∧
        certifiedRow (equation.solutionWidth + equation.moduli.size)
          (certShift equation shift bound) bound bRow = true ∧
        ((List.range equation.solutionWidth).map fun j ↦ rowGet bRow j).toArray = row := by
  unfold certifiedSolutionBasis
  split
  · rename_i hg
    simp only [MatrixRows, principalSolutionRows, Array.toList_map, List.mem_map,
      Array.toList_filter, List.mem_filter, hg, true_and]
    constructor
    · rintro ⟨b, ⟨hb, hc⟩, rfl⟩
      exact ⟨b, hb, hc, rfl⟩
    · rintro ⟨b, hb, hc, rfl⟩
      exact ⟨b, ⟨hb, hc⟩, rfl⟩
  · rename_i hg
    simp [MatrixRows, hg]

theorem certifiedSolutionBasis_sound {mulCtx : CPolynomial.MulContext F}
    {modCtx : CPolynomial.ModContext F} {pmCtx : PMBasisContext F}
    {equation : ModularEquation F} {shift : Array Nat} {bound : Nat} {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (certifiedSolutionBasis modCtx pmCtx equation shift bound)) :
    rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true := by
  obtain ⟨hg, bRow, hbMem, hc, rfl⟩ := mem_certifiedSolutionBasis.1 hrow
  obtain ⟨hpos, hshift, hcols, hmonic⟩ := certifiedGuard_iff.1 hg
  obtain ⟨hsize, D, hD, hD2⟩ := certifiedRow_iff.1 hc
  exact (certifiedRow_sound mulCtx modCtx pmCtx equation shift bound hmonic hcols hshift hpos
    hbMem hD hsize hD2).1

theorem certifiedSolutionBasis_width {modCtx : CPolynomial.ModContext F}
    {pmCtx : PMBasisContext F} {equation : ModularEquation F} {shift : Array Nat} {bound : Nat}
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (certifiedSolutionBasis modCtx pmCtx equation shift bound)) :
    row.size = equation.solutionWidth := by
  obtain ⟨-, bRow, -, -, rfl⟩ := mem_certifiedSolutionBasis.1 hrow
  simp

/-- **Domination**: a nonzero in-width solution of shifted degree `e ≤ bound` is dominated by a
row of the certified solve. -/
theorem certifiedSolutionBasis_dominates (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (bound : Nat) {rowStar : PolynomialRow F} {e : Nat}
    (hmonic : ∀ b, b < equation.moduli.size → (equation.moduli.getD b 0).monic)
    (hcols : equation.moduli.size ≤ MatrixWidth equation.matrix)
    (hshift : shift.size = equation.solutionWidth)
    (hsat : rowSatisfiesModularBool mulCtx modCtx rowStar equation.matrix
      equation.moduli = true)
    (hnz : rowIsZero rowStar = false)
    (hwidth : rowStar.size ≤ equation.solutionWidth)
    (hdeg : rowShiftedDegree? rowStar shift = some e)
    (hebound : e ≤ bound) :
    ∃ basisRow degree,
      basisRow ∈ MatrixRows (certifiedSolutionBasis modCtx pmCtx equation shift bound) ∧
      rowShiftedDegree? basisRow shift = some degree ∧ degree ≤ e := by
  obtain ⟨j0, hj0, -⟩ := exists_nonzero_entry_of_rowIsZero_false hnz
  have hpos : 0 < equation.solutionWidth := by omega
  obtain ⟨bRow, Db, hbMem, hbSize, hbDeg, hDb⟩ := certifiedRow_complete mulCtx modCtx pmCtx
    equation shift bound hmonic hcols hshift hpos hsat hnz hwidth hdeg
  obtain ⟨-, -, degB, hdegB, hle⟩ := certifiedRow_sound mulCtx modCtx pmCtx equation shift bound
    hmonic hcols hshift hpos hbMem hbDeg hbSize (by omega)
  refine ⟨_, degB, mem_certifiedSolutionBasis.2 ⟨certifiedGuard_iff.2 ⟨hpos, hshift, hcols,
    hmonic⟩, bRow, hbMem, certifiedRow_iff.2 ⟨hbSize, Db, hbDeg, by omega⟩, rfl⟩, hdegB, by omega⟩

/-- **The certified solver as CompPoly's solution-basis context**, at the caller's bound (the
full pivot window without one). -/
@[expose] def certifiedModularSolutionBasisContext (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (pmCtx : PMBasisContext F) :
    ModularSolutionBasisContext F where
  mulContext := mulCtx
  modContext := modCtx
  solutionBasis equation shift degreeBound? :=
    certifiedSolutionBasis modCtx pmCtx equation shift (solveWindow equation shift degreeBound?)
  sound := fun _ _ _ _ hrow ↦ certifiedSolutionBasis_sound hrow
  complete_minimal := by
    intro equation shift degreeBound? row d hmonic hcols hshift hsat hnz hwidth hd hdbound
    refine ⟨fun _ h ↦ le_of_eq (certifiedSolutionBasis_width h), ?_⟩
    obtain ⟨j0, hj0, -⟩ := exists_nonzero_entry_of_rowIsZero_false hnz
    cases hbnd : degreeBound? with
    | some bound =>
      have hdb : d ≤ bound := hdbound bound hbnd
      obtain ⟨bRow, degB, hmem, hdegB, hleB⟩ := certifiedSolutionBasis_dominates mulCtx modCtx
        pmCtx equation shift bound hmonic hcols hshift hsat hnz hwidth hd hdb
      exact ⟨bRow, degB, hmem, hdegB, by rw [Option.getD_some]; omega⟩
    | none =>
      have hwin : solveWindow equation shift none =
          pivotWindowCap equation + maxShiftDegree shift := rfl
      by_cases hdw : d ≤ pivotWindowCap equation + maxShiftDegree shift
      · obtain ⟨bRow, degB, hmem, hdegB, hleB⟩ := certifiedSolutionBasis_dominates mulCtx modCtx
          pmCtx equation shift _ hmonic hcols hshift hsat hnz hwidth hd (hwin ▸ hdw)
        exact ⟨bRow, degB, hmem, hdegB, by rw [Option.getD_none]; omega⟩
      · obtain ⟨prow, e, hsatP, hnzP, hsizeP, hdegP, heP⟩ :=
          me_prodRow_facts mulCtx modCtx equation shift (p := j0) hmonic hcols (by omega)
        obtain ⟨bRow, degB, hmem, hdegB, hleB⟩ := certifiedSolutionBasis_dominates mulCtx modCtx
          pmCtx equation shift _ hmonic hcols hshift hsatP hnzP (le_of_eq hsizeP) hdegP
          (hwin ▸ heP)
        exact ⟨bRow, degB, hmem, hdegB, by rw [Option.getD_none]; omega⟩

end

end LeanVM.Extraction.Fast
