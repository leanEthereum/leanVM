module

public import LeanVM.Cost.Bounds.PMFFT.EvalCost
public import LeanVM.Cost.Bounds.PMBasis.LaneDefs

/-!
# Bounds of the PM decoder's FFT: the univariate product

`fftMulContext`'s product (`mulViaFFTC`, `FFT.mulVia novelTransform fftSchedule`) on its transform
branch (both factors above `32` coefficients, one above `4096`): two forward transforms, the
pointwise product, one inverse, the plan; within `polyMulPrice`.
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Cost.Bounds.PMBasis

public section

variable (P : MachineProgram)

/-- **The pointwise product** (`pmul.c415`) of `n` entries: at most `55·n + 16`. -/
theorem pmulC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.FFT.pmul.c415.costDeps) (n : ℕ)
    (hn : n < 2 ^ 64) (a b : Array K) :
    machineCost P Auto.LeanVM.Extraction.Fast.FFT.pmul.c415.costIdx [encodeValue n, encodeValue a,
      encodeValue b] ≤ 55 * n + 16 := by
  rw [Auto.LeanVM.Extraction.Fast.FFT.pmul.c415.costEq P hP]
  have hof := ofFnFrom_cost P (by includes) hn _
    (.closure Auto.LeanVM.Extraction.Fast.FFT.pmul.c415.lam0.costIdx [encodeValue n, encodeValue a,
      encodeValue b])
    (fun v ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.Fast.FFT.pmul.c415.lam0.costSpec P (by includes)
      n a b v)) 38
    (fun v ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Extraction.Fast.FFT.pmul.c415.lam0.costEq P (by includes)]) 0 (Nat.zero_le _)
  rw [ofFnFrom_length]
  simp only [Nat.sub_zero] at hof
  omega

theorem logAbove_eq_clog2 {n : ℕ} (hn : 1 ≤ n) : FFT.logAbove n = clog2 (n + 1) := by
  apply le_antisymm
  · -- 2^(clog2 (n+1)) ≥ n + 1 > n, and logAbove n is the least `j` with `n < 2^j`
    have h1 : n + 1 ≤ 2 ^ clog2 (n + 1) := by
      rw [clog2_eq_ceilLog]; exact EvalMat.le_two_pow_ceilLog _
    unfold FFT.logAbove
    have := (Nat.log2_lt (n := n) (k := clog2 (n + 1)) (by omega)).2 (by omega)
    omega
  · have := FFT.lt_two_pow_logAbove n
    exact clog2_le (by omega)

/-- **`fftMulContext`'s product on its transform branch** (`mulViaFFTC`): both factors above `32`
coefficients, one above `4096`, `|f| + |g| − 1 ≤ 2^36`: within `polyMulPrice` at
`clog2 (|f| + |g| − 1)`. -/
theorem mulViaFFTC_cost_fft (hP : Includes P mulViaFFTC.costDeps) (p : PMPrices) (hp : FFTPricesOK p)
    (f g : CompPoly.CPolynomial K) (hf : 32 < f.val.size) (hg : 32 < g.val.size)
    (hbig : 4096 < f.val.size ∨ 4096 < g.val.size)
    (hj : f.val.size + g.val.size - 1 ≤ 2 ^ 36) :
    machineCost P mulViaFFTC.costIdx [encodeValue f, encodeValue g] ≤
      polyMulPrice p (clog2 (f.val.size + g.val.size - 1)) := by
  rw [mulViaFFTC.costEq P hP]
  have hs : FFT.fftSchedule.small = 32 := rfl
  have hm : FFT.fftSchedule.mid = 4096 := rfl
  have hlog : limbCount FFT.novelTransform.maxLog = 1 := limbs_of_lt (show 64 < 2 ^ 64 by norm_num)
  set a := f.val.size
  set b := g.val.size
  have hJ : FFT.logAbove (a + b - 2) = clog2 (a + b - 1) := by
    rw [logAbove_eq_clog2 (by omega)]; congr 1; omega
  set J := FFT.logAbove (a + b - 2)
  have hJ36 : J ≤ 36 := by rw [hJ]; exact clog2_le hj
  have hJ64 : J ≤ FFT.novelTransform.maxLog := by show J ≤ 64; omega
  rw [hs, hm, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hJ64]
  simp only [novelTransform_plan]
  have hJ40 : J ≤ 40 := by omega
  have hN : 2 ^ J ≤ 2 ^ 36 := Nat.pow_le_pow_right (by norm_num) hJ36
  have h1 := mkPlanC_cost P (by includes) hJ40
  have h2 := planFwdPolyC_cost P (by includes) hJ40 f
  have h3 := planFwdPolyC_cost P (by includes) hJ40 g
  have h4 := pmulC_cost P (by includes) (2 ^ J) (by omega) (FFT.novelTransform.fwdP (FFT.mkPlan J) f)
    (FFT.novelTransform.fwdP (FFT.mkPlan J) g)
  have h5 := planInvPolyC_cost P (by includes) hJ40 (FFT.pmul (2 ^ J)
    (FFT.novelTransform.fwdP (FFT.mkPlan J) f) (FFT.novelTransform.fwdP (FFT.mkPlan J) g))
  have h6 := log2Rec_cost_word P (by includes) (a + b - 2) (by omega)
  have hl2 : Nat.log2 (a + b - 2) ≤ 36 := by
    have := FFT.lt_two_pow_logAbove (a + b - 2)
    have : Nat.log2 (a + b - 2) < J := by simp only [J, FFT.logAbove]; omega
    omega
  rw [limbs_shift (k := J) (by omega)]
  cost_simp
  -- within the model
  obtain ⟨hmac, hneed⟩ := hp
  obtain ⟨hfw, hiv⟩ := hneed J (by omega)
  rw [← hJ, polyMulPrice]
  have hpl := plan_fit 1 J (le_refl 1)
  have hmacN : 80 * 2 ^ J ≤ p.mac * 2 ^ J := Nat.mul_le_mul_right _ hmac
  have hfw' : fwdBound J ≤ fwdNeed J := by unfold fwdNeed; omega
  unfold invNeed at hiv
  simp only [Nat.one_mul] at hpl
  rw [fwdBound] at hfw' hpl
  rw [invBound] at hiv
  rw [planBound] at hpl
  split_ifs <;> omega

end

end LeanVM.Cost.Bounds.PMFFT
