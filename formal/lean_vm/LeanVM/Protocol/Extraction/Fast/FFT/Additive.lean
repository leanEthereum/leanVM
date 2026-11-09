module

public import LeanVM.Protocol.Extraction.Fast.FFT.Convert
public import LeanVM.Protocol.Extraction.Fast.FFT.Transform
public import LeanVM.Protocol.Extraction.Fast.Karatsuba
import all CompPoly.Univariate.Basic

/-!
# The additive FFT over `K`: transform, product, contexts

**The transform** (`novelTransform : PointTransform K FFTPlan`, `maxLog = 64`, points
`x_v = K.ofBits v`), through the plan `mkPlan j` (`Fast/FFT/Plan.lean`, built once per size):
`fwdP P p` (`planFwdPoly`) converts `p`'s monomial coefficients to the novel basis
(`toNovelInPlace`, in place level by level, `Fast/FFT/Convert`) and evaluates on
`U_j = {x_v | v < 2^j}` by the additive NTT with the plan's twiddles (`planFwd`); `invP P y` (`planInvPoly`) interpolates
(`planInv`) and converts back (`fromNovelInPlace`). By the plan they are the unplanned
`novelFwdPoly j` (`toNovel j`, `novelFwd j 0`) and `novelInvPoly j` (`novelInv j`, `fromNovel j`)
(`planFwdPoly_eq`, `planInvPoly_eq`), whose laws come from `novelFwd_getD`, `novelInv_eval`,
`novelFwd_novelInv` and the conversions' `toNovel_spec`, `fromNovel_spec`.
`FFT/PlannedEval.lean`'s evaluation-domain matrix products use it, the plan built once per
matrix product.

**The product** `mulFFT p q` (`mulVia novelTransform fftSchedule`): schoolbook when a factor has
at most `32` coefficients, Karatsuba's when both have at most `4096`, else on the least
`2^j ≥ |p| + |q| − 1` points (`j ≤ 64`, else Karatsuba's), the plan built once;
`mulFFT_eq : mulFFT p q = p * q`. CompPoly's contexts: `fftMulContext`, `fftMulLowContext` (the
truncated product as one product of truncated factors), `fftRawMulLowContext`, and
`fftModContext` (monic remainders by reversal on it).

**Cost** (`K` products, `N = 2^j`, counted on the definitions, every `*` executed): the
conversions `toNovelInPlace`, `fromNovelInPlace` exactly `N·j(j+1)/4` each (`1.5·N` and `N` array
entries per level, the sparse sums stopping at the first vanishing term) (the division by `W_i`, or
the product by it, at level `i` is `(i+1)·2^i` per block of `2^(i+1)`); `planFwd` and `planInv`
`N·j/2` each (one product per butterfly and stage, `fwdStageFast`, `invStageFast`); so `fwdP`
and `invP` `N·(j² + 3j)/4` each, no inversion, and no power of two computed per entry (the
plan's `pows`, the stages' `2^i` once per stage); the product
`2·fwdP + N + invP = N·(3j² + 9j + 4)/4`. The plan:
the table `2 + Σ_{1≤J<j} (4J + 3)`, the batched inverses `3j` and one inversion, the twiddles
`Σ_{i<j} (j−i−1)(2i+3)` products and `< N` additions (`17464` products at `j = 35`).
-/

namespace LeanVM.Extraction.Fast.FFT

open CompPoly LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.NovelProofs Polynomial

public section

/-! ## Polynomials of arrays -/

theorem polyN_val {n : ℕ} (p : CPolynomial K) (hp : p.val.size ≤ n) : polyN n p.val = p.toPoly := by
  refine Polynomial.ext fun d ↦ ?_
  rw [coeff_polyN, CPolynomial.toPoly_coeff]
  split
  · rfl
  · rw [CPolynomial.coeff_eq_zero_of_size_le _ (by omega)]

theorem toPoly_ofArray (a : Array K) : (CPolynomial.ofArray a).toPoly = polyN a.size a := by
  refine Polynomial.ext fun d ↦ ?_
  rw [coeff_polyN, CPolynomial.toPoly_coeff, CPolynomial.coeff_ofArray]
  split
  · rfl
  · rfl

theorem size_ofArray_le (a : Array K) : (CPolynomial.ofArray a).val.size ≤ a.size :=
  size_le_of_coeff_eq_zero _ fun i hi ↦ by
    rw [CPolynomial.coeff_ofArray, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi,
      Option.getD_none]

theorem ofFn_getD_self {n : ℕ} (c : Array K) (hc : c.size = n) :
    (Array.ofFn fun t : Fin n ↦ c.getD t.val 0) = c := by
  apply array_eq_of_getD (by rw [Array.size_ofFn, hc])
  intro p hp
  rw [Array.size_ofFn] at hp
  rw [getD_ofFn _ hp]

/-! ## The transform -/

/-- The evaluations on `U_j` of `p`'s first `2^j` coefficients. -/
@[expose] def novelFwdPoly (j : ℕ) (p : CPolynomial K) : Array K := novelFwd j 0 (toNovel j p.val)

/-- The polynomial of at most `2^j` coefficients with the values `y` on `U_j`. -/
@[expose] def novelInvPoly (j : ℕ) (y : Array K) : CPolynomial K :=
  CPolynomial.ofArray (fromNovel j (novelInv j y))

theorem getD_novelFwd_eval {j : ℕ} (hj : j ≤ 64) (c : Array K) {v : ℕ} (hv : v < 2 ^ j) :
    (novelFwd j 0 c).getD v 0 = (novelSum (2 ^ j) c).eval (K.ofBits v) := by
  rw [novelFwd_getD hj c (by simpa using hv), eval_novelSum]

theorem novelFwdPoly_getD {j : ℕ} (hj : j ≤ 64) (p : CPolynomial K) (hp : p.val.size ≤ 2 ^ j)
    {v : ℕ} (hv : v < 2 ^ j) : (novelFwdPoly j p).getD v 0 = p.eval (K.ofBits v) := by
  rw [novelFwdPoly, getD_novelFwd_eval hj _ hv, (toNovel_spec hj _).2, polyN_val p hp,
    CPolynomial.eval_toPoly]

theorem toPoly_novelInvPoly {j : ℕ} (hj : j ≤ 64) (y : Array K) :
    (novelInvPoly j y).toPoly = novelSum (2 ^ j) (novelInv j y) := by
  rw [novelInvPoly, toPoly_ofArray, (fromNovel_spec hj _).1, (fromNovel_spec hj _).2]

theorem size_novelInvPoly {j : ℕ} (hj : j ≤ 64) (y : Array K) :
    (novelInvPoly j y).val.size ≤ 2 ^ j :=
  (size_ofArray_le _).trans (fromNovel_spec hj _).1.le

theorem novelInvPoly_eq {j : ℕ} (hj : j ≤ 64) (y : Array K) (p : CPolynomial K)
    (hy : y.size = 2 ^ j) (hp : p.val.size ≤ 2 ^ j)
    (hval : ∀ v < 2 ^ j, y.getD v 0 = p.eval (K.ofBits v)) : novelInvPoly j y = p := by
  have hc := (toNovel_spec hj p.val).1
  have hinv : novelInv j y = toNovel j p.val := by
    rw [novelInv_eval hj (fun t ↦ (toNovel j p.val).getD t 0) y hy fun v hv ↦ by
      rw [hval v hv, CPolynomial.eval_toPoly, ← polyN_val p hp, ← (toNovel_spec hj _).2,
        eval_novelSum], ofFn_getD_self _ hc]
  apply CPolynomial.toPoly_injective
  rw [toPoly_novelInvPoly hj y, hinv, (toNovel_spec hj _).2, polyN_val p hp]

theorem novelFwdPoly_novelInvPoly {j : ℕ} (hj : j ≤ 64) (y : Array K) (hy : y.size = 2 ^ j) :
    novelFwdPoly j (novelInvPoly j y) = y := by
  have hsz : (novelFwdPoly j (novelInvPoly j y)).size = 2 ^ j := by
    rw [novelFwdPoly, size_novelFwd, Nat.add_zero]
  apply array_eq_of_getD (by rw [hsz, hy])
  intro v hv
  rw [hsz] at hv
  rw [novelFwdPoly_getD hj _ (size_novelInvPoly hj y) hv, CPolynomial.eval_toPoly,
    toPoly_novelInvPoly hj y, ← getD_novelFwd_eval hj _ hv, novelFwd_novelInv y hy]

/-! ## The planned transform -/

/-- The evaluations by the plan: monomial → novel in place (`toNovelInPlace`), then `planFwd`. -/
@[expose] def planFwdPoly (P : FFTPlan) (p : CPolynomial K) : Array K :=
  planFwd P (toNovelInPlace P p.val)

/-- The interpolation by the plan: `planInv`, then novel → monomial in place
(`fromNovelInPlace`). -/
@[expose] def planInvPoly (P : FFTPlan) (y : Array K) : CPolynomial K :=
  CPolynomial.ofArray (fromNovelInPlace P (planInv P y))

theorem planFwdPoly_eq {j : ℕ} (hj : j ≤ 64) (p : CPolynomial K) :
    planFwdPoly (mkPlan j) p = novelFwdPoly j p := by
  rw [planFwdPoly, toNovelInPlace_eq hj, planFwd_eq hj]
  rfl

theorem planInvPoly_eq {j : ℕ} (hj : j ≤ 64) (y : Array K) :
    planInvPoly (mkPlan j) y = novelInvPoly j y := by
  rw [planInvPoly, planInv_eq hj, fromNovelInPlace_eq hj]
  rfl

/-- **The novel-basis transform** over `K`: `2^j` points `x_v`, `j ≤ 64`, through the plan
`mkPlan j`. -/
@[expose] def novelTransform : PointTransform K FFTPlan where
  maxLog := 64
  point v := K.ofBits v
  plan := mkPlan
  fwdP := planFwdPoly
  invP := planInvPoly
  size_fwd p hj := by rw [planFwdPoly_eq hj, novelFwdPoly, size_novelFwd, Nat.add_zero]
  fwd_getD p hj hp _ hv := by rw [planFwdPoly_eq hj]; exact novelFwdPoly_getD hj p hp hv
  inv_eq y p hj hy hp hval := by rw [planInvPoly_eq hj]; exact novelInvPoly_eq hj y p hy hp hval
  size_inv y hj _ := by rw [planInvPoly_eq hj]; exact size_novelInvPoly hj y
  fwd_inv y hj hy := by
    rw [planInvPoly_eq hj, planFwdPoly_eq hj]; exact novelFwdPoly_novelInvPoly hj y hy

/-! ## The product and CompPoly's contexts -/

/-- The schedule: schoolbook when a factor has at most `32` coefficients, Karatsuba's product
when both have at most `4096` (the compiled prices measured: at `1100`
coefficients the transform's product `238M` steps against Karatsuba's `76M`, at `2100` `540M`
against `214M`; the crossover near `4096`). -/
@[expose] def fftSchedule : MulSchedule K where
  small := 32
  mid := 4096
  fallback := karatsubaMulContext

/-- **The additive-FFT product** over `K`. -/
@[expose] def mulFFT (p q : CPolynomial K) : CPolynomial K := mulVia novelTransform fftSchedule p q

theorem mulFFT_eq (p q : CPolynomial K) : mulFFT p q = p * q := mulVia_eq _ _ p q

/-- CompPoly's multiplication context for the additive-FFT product. -/
@[expose] def fftMulContext : CPolynomial.MulContext K := mulContextOf novelTransform fftSchedule

/-- CompPoly's polynomial-matrix low-product context for the additive-FFT product. -/
@[expose] def fftMulLowContext : PolynomialMatrix.MulLowContext K :=
  mulLowContextOf novelTransform fftSchedule

/-- CompPoly's raw low-product context for the additive-FFT product. -/
@[expose] def fftRawMulLowContext : CPolynomial.Raw.MulLowContext K :=
  rawMulLowContextOf novelTransform fftSchedule

/-- CompPoly's monic-remainder context by reversal, on the additive-FFT low products. -/
@[expose] def fftModContext : CPolynomial.ModContext K :=
  CPolynomial.ModContext.reversal fftRawMulLowContext

end

end LeanVM.Extraction.Fast.FFT
