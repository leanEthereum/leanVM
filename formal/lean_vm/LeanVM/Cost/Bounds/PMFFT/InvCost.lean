module

public import LeanVM.Cost.Bounds.PMFFT.KarCost
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic
public import LeanVM.Cost.Bounds.Decoder.Poly

public import LeanVM.Cost.Bounds.PMLane.InterpDefs
/-!
# Bounds of the PM decoder's FFT: low products, Newton's inverse, the remainder

`fftRawMulLowContext`'s low product (`rawMulLowFFTC`: both factors truncated at `k`, one product),
Newton's inverse modulo `X^k` on it (`inverseModXFFTC`: precisions `2, 4, …, k`, two low products
each, the products' prices doubling with the size so their sum at most twice the last).
`fftModContext`'s remainder by reversal is bounded in `Bounds/PMSolve/Remainder.lean`.
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Cost.Bounds.PMBasis

public section

variable (P : MachineProgram)

theorem polyMulPrice_mono (p : PMPrices) {a b : ℕ} (h : a ≤ b) : polyMulPrice p a ≤ polyMulPrice p b := by
  unfold polyMulPrice
  have := fwdPrice_mono p h
  have := invPrice_mono p h
  have := Nat.mul_le_mul_left p.mac (Nat.pow_le_pow_right (show 0 < 2 by norm_num) h)
  omega

/-- **The low product** (`rawMulLowFFTC`, `fftRawMulLowContext.mulLow k`), `1 ≤ k ≤ 2^35`: at most
`polyMulPrice p (clog2 (2k − 1)) + karMax + 45·k + 42`. -/
theorem rawMulLowFFTC_cost (hP : Includes P rawMulLowFFTC.costDeps) (p : PMPrices) (hp : FFTPricesOK p)
    (k : ℕ) (hk : k ≤ 2 ^ 35) (a b : CompPoly.CPolynomial.Raw K) :
    machineCost P rawMulLowFFTC.costIdx [encodeValue k, encodeValue a, encodeValue b] ≤
      polyMulPrice p (clog2 (2 * k - 1)) + karMax + 45 * k + 42 := by
  rw [rawMulLowFFTC.costEq P hP]
  have ha : (a.extract 0 k).size ≤ k := by simp
  have hb : (b.extract 0 k).size ≤ k := by simp
  have h1 := Decoder.ofArray_cost P (by includes) (a.extract 0 k) (by omega)
  have h2 := Decoder.ofArray_cost P (by includes) (b.extract 0 k) (by omega)
  have sa := FFT.size_ofArray_le (a.extract 0 k)
  have sb := FFT.size_ofArray_le (b.extract 0 k)
  have hm := mulViaFFTC_cost P (by includes) p hp (CompPoly.CPolynomial.ofArray (a.extract 0 k))
    (CompPoly.CPolynomial.ofArray (b.extract 0 k)) (by omega)
  have hmono := polyMulPrice_mono p (clog2_mono (show
    (CompPoly.CPolynomial.ofArray (a.extract 0 k)).val.size +
      (CompPoly.CPolynomial.ofArray (b.extract 0 k)).val.size - 1 ≤ 2 * k - 1 by omega))
  have hr : (Array.extract (FFT.mulVia FFT.novelTransform FFT.fftSchedule
      (CompPoly.CPolynomial.ofArray (a.extract 0 k)) (CompPoly.CPolynomial.ofArray (b.extract 0 k))).val
      0 k).size ≤ k := by simp
  omega

/-- **A subtraction of raw polynomials** (`Raw.sub.c49`): at most `71·max(|x|, |y|) + 72`. -/
theorem subC_cost (hP : Includes P Auto.CompPoly.CPolynomial.Raw.sub.c49.costDeps)
    (x y : CompPoly.CPolynomial.Raw K) (hx : x.size < 2 ^ 40) (hy : y.size < 2 ^ 40) :
    machineCost P Auto.CompPoly.CPolynomial.Raw.sub.c49.costIdx [encodeValue x, encodeValue y] ≤
      71 * max x.size y.size + 72 := by
  rw [Auto.CompPoly.CPolynomial.Raw.sub.c49.costEq P hP]
  have hm := map_cost P (by includes) (fun a : K ↦ -a)
    (.closure Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costSpec P (by includes) a)) 1
    y.toList (fun a _ ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]
      rw [Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costEq P (by includes)])
  have hn : (CompPoly.CPolynomial.Raw.neg y).size = y.size := by
    simp [CompPoly.CPolynomial.Raw.neg]
  have ha := Decoder.addK_cost P (by includes) x (CompPoly.CPolynomial.Raw.neg y) (by omega) (by omega)
  rw [hn] at ha
  simp only [Array.length_toList, List.length_map] at hm ⊢
  have : max x.size y.size ≥ y.size := le_max_right _ _
  omega

/-- A product over twice the points costs at least twice as much, but for the `2^20`. -/
theorem polyMulPrice_succ (p : PMPrices) (j : ℕ) :
    2 * polyMulPrice p j ≤ polyMulPrice p (j + 1) + 2 ^ 20 := by
  unfold polyMulPrice fwdPrice invPrice
  rw [show 2 ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j]
  generalize 2 ^ j = X
  nlinarith [Nat.zero_le ((p.toNovel + p.fwd) * X), Nat.zero_le ((p.fromNovel + p.inv) * X)]

/-- Newton's precision doubling from `2^i` to `k' > 2^i`: four products at the former within two
at the latter. -/
theorem polyMulPrice_newton (p : PMPrices) {i k' : ℕ} (h : 2 ^ i < k') :
    4 * polyMulPrice p (clog2 (2 * 2 ^ i - 1)) ≤ 2 * polyMulPrice p (clog2 (2 * k' - 1)) + 2 ^ 21 := by
  have h1 : clog2 (2 * 2 ^ i - 1) ≤ i + 1 := PMBasis.clog2_le (by rw [pow_succ]; omega)
  have h2 : i + 1 + 1 ≤ clog2 (2 * k' - 1) := by
    by_contra hc
    have e1 := PMBasis.le_two_pow_clog2 (2 * k' - 1)
    have e2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show clog2 (2 * k' - 1) ≤ i + 1 by omega)
    rw [pow_succ] at e2
    omega
  have := polyMulPrice_succ p (i + 1)
  have := polyMulPrice_mono p h1
  have := polyMulPrice_mono p h2
  omega

/-- **Newton's loop** (`inverseModX.go.c421`) from precision `a ≤ k` with `k ≤ a·2^m`, `a` a power
of two or `k`: its price and four products at precision `a` within four at `k` and
`m · newtonExtra k + k + 18`. -/
theorem newtonGo_cost (hP : Includes P Auto.CompPoly.CPolynomial.Raw.inverseModX.go.c421.costDeps)
    (p : PMPrices) (hp : FFTPricesOK p) (k : ℕ) (hk : k ≤ 2 ^ 35) (f : CompPoly.CPolynomial.Raw K) :
    ∀ m fuel a (acc : CompPoly.CPolynomial.Raw K), 1 ≤ a → a ≤ k → k ≤ a * 2 ^ m → fuel < 2 ^ 64 →
      (a = k ∨ ∃ i, a = 2 ^ i) →
      machineCost P Auto.CompPoly.CPolynomial.Raw.inverseModX.go.c421.costIdx [encodeValue k,
        encodeValue f, encodeValue fuel, encodeValue a, encodeValue acc] +
          4 * polyMulPrice p (clog2 (2 * a - 1)) ≤
        4 * polyMulPrice p (clog2 (2 * k - 1)) + m * newtonExtra k + k + 18 := by
  intro m
  induction m with
  | zero =>
    intro fuel a acc ha hak hkm hf _
    have hs : (acc.extract 0 k).size ≤ k := by simp
    have hmono := polyMulPrice_mono p (clog2_mono (show 2 * a - 1 ≤ 2 * k - 1 by omega))
    rw [Auto.CompPoly.CPolynomial.Raw.inverseModX.go.c421.costEq P hP]
    cases fuel with
    | zero => cost_simp; omega
    | succ n =>
      cost_simp
      rw [ite_eq_left (by simpa using hkm)]
      omega
  | succ m ih =>
    intro fuel a acc ha hak hkm hf hpow
    have hs : (acc.extract 0 k).size ≤ k := by simp
    have hmono := polyMulPrice_mono p (clog2_mono (show 2 * a - 1 ≤ 2 * k - 1 by omega))
    rw [Auto.CompPoly.CPolynomial.Raw.inverseModX.go.c421.costEq P hP]
    cases fuel with
    | zero => cost_simp; omega
    | succ n =>
      cost_simp
      by_cases hka : k ≤ a
      · rw [ite_eq_left hka]; omega
      · rw [ite_eq_right hka]
        obtain ⟨i, hi⟩ : ∃ i, a = 2 ^ i := hpow.resolve_left (by omega)
        set k' := min k (2 * a) with hk'
        rw [show k.min (2 * a) = k' from rfl]
        have hk'k : k' ≤ k := min_le_left _ _
        have hk'1 : 1 ≤ k' := by omega
        have hak' : a < k' := by omega
        have r1 := rawMulLowFFTC_cost P (by includes) p hp k' (by omega) f acc
        have hml := FFT.fftRawMulLowContext.size_le k' f acc
        have hC : (CompPoly.CPolynomial.Raw.C (2 : K)).size = 1 := rfl
        have s1 := subC_cost P (by includes) (CompPoly.CPolynomial.Raw.C 2)
          (FFT.fftRawMulLowContext.mulLow k' f acc) (by omega) (by omega)
        have r2 := rawMulLowFFTC_cost P (by includes) p hp k' (by omega) acc
          (CompPoly.CPolynomial.Raw.C 2 - FFT.fftRawMulLowContext.mulLow k' f acc)
        have hrec := ih n k' (FFT.fftRawMulLowContext.mulLow k' acc
          (CompPoly.CPolynomial.Raw.C 2 - FFT.fftRawMulLowContext.mulLow k' f acc)) hk'1 hk'k
          (by
            rcases Nat.le_total k (2 * a) with h | h
            · have : k' = k := by omega
              rw [this]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
            · have : k' = 2 * a := by omega
              rw [this, pow_succ] at *; nlinarith) (by omega)
          (by
            rcases Nat.le_total k (2 * a) with h | h
            · left; omega
            · right; exact ⟨i + 1, by rw [pow_succ]; omega⟩)
        have hnew := polyMulPrice_newton p (i := i) (k' := k') (by omega)
        rw [← hi] at hnew
        have hmax : max (CompPoly.CPolynomial.Raw.C (2 : K)).size
            (FFT.fftRawMulLowContext.mulLow k' f acc).size ≤ k' := by rw [hC]; omega
        unfold newtonExtra at hrec ⊢
        have e : (m + 1) * (2 * karMax + 161 * k + 2 ^ 21 + 207) =
            m * (2 * karMax + 161 * k + 2 ^ 21 + 207) + (2 * karMax + 161 * k + 2 ^ 21 + 207) := by
          ring
        rw [e]
        split_ifs <;> omega

/-- **Newton's inverse modulo `X^k`** (`inverseModXFFTC`), `k ≤ 2^35`: at most
`newtonBound p k` (four products at precision `k`, `⌈log₂ k⌉` steps' extras, one inversion). -/
theorem inverseModXFFTC_cost (hP : Includes P inverseModXFFTC.costDeps) (p : PMPrices)
    (hp : FFTPricesOK p) (k : ℕ) (hk : k ≤ 2 ^ 35) (f : CompPoly.CPolynomial.Raw K) :
    machineCost P inverseModXFFTC.costIdx [encodeValue k, encodeValue f] ≤ newtonBound p k := by
  rw [inverseModXFFTC.costEq P hP]
  unfold newtonBound
  by_cases hk0 : k = 0
  · simp [hk0]
  · rw [ite_eq_right hk0]
    have hc := PMBasis.le_two_pow_clog2 k
    have h1 := invK_cost P (by includes) (f.coeff 0)
    have h2 := newtonGo_cost P (by includes) p hp k hk f (clog2 k) (k + 1) 1
      (CompPoly.CPolynomial.Raw.C (f.coeff 0)⁻¹) le_rfl (by omega) (by omega) (by omega)
      (Or.inr ⟨0, rfl⟩)
    cost_simp
    omega

theorem newtonExtra_mono {a b : ℕ} (h : a ≤ b) : newtonExtra a ≤ newtonExtra b := by
  unfold newtonExtra; omega

theorem newtonBound_mono (p : PMPrices) {a b : ℕ} (h : a ≤ b) : newtonBound p a ≤ newtonBound p b := by
  unfold newtonBound
  have := polyMulPrice_mono p (clog2_mono (show 2 * a - 1 ≤ 2 * b - 1 by omega))
  have := Nat.mul_le_mul (clog2_mono h) (newtonExtra_mono h)
  omega

end

end LeanVM.Cost.Bounds.PMFFT
