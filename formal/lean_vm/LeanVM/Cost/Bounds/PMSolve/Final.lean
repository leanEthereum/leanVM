module

public import LeanVM.Cost.Bounds.PMSolve.Interp
public import LeanVM.Cost.Bounds.PMFFT.InvCost
public import LeanVM.Cost.Bounds.PMCore.Leaf
public import LeanVM.Cost.Bounds.PMBasis.Values

public import LeanVM.Cost.Bounds.PMLane.InterpDefs
/-!
# Bounds: the lanes' interpolation within its price, the hypotheses discharged

The products of at most `N` coefficients, the truncated products and Newton's inverses at
precision `≤ N` (`mulViaFFTC_cost`, `rawMulLowFFTC_cost`, `inverseModXFFTC_cost`):
`mulBound_fft`, `lowBound_fft`, `invBound_fft`, at the prices `fftMB`, `fftLB`, `fftIB`; the
PM-basis core (`pmCoreC_cost`, the leaf's `leafCost`) at the leaf's proved price
`leafBound r m + 21·m + 32`: `pmCoreCostAt_leaf`.

**`interpolatePMC_cost_model`**: the lanes' interpolation at most `interpPMModel p n params`, on
the shapes `PMInterpOK n params` (decidable: the sizes, the transforms within `2^36` points, the
core's shift bound). **`interpolatePMC_cost_price`**: within the model's `interpPMPrice` where
`interpPMModel ≤ interpPMPrice` (decidable, per shape).
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open LeanVM.Cost.Bounds.PMBasis

public section

/-- **The margin prices fit the transforms' and products' proved prices.** -/
theorem fftPricesOK_margin : PMFFT.FFTPricesOK marginPrices := by decide +kernel

variable (P : MachineProgram)

theorem mulBound_fft (hP : Includes P mulViaFFTC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) (N : ℕ) (hN : N ≤ 2 ^ 36) : MulBound P N (fftMB p N) := by
  intro f g hfg
  have := PMFFT.mulViaFFTC_cost P hP p hp f g (by omega)
  have := PMFFT.polyMulPrice_mono p (clog2_mono (show f.val.size + g.val.size - 1 ≤ N by omega))
  unfold fftMB
  unfold PMFFT.karMax at *
  omega

theorem lowBound_fft (hP : Includes P rawMulLowFFTC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) (N : ℕ) (hN : N ≤ 2 ^ 35) : LowBound P N (fftLB p N) := by
  intro k a b hk
  have := PMFFT.rawMulLowFFTC_cost P hP p hp k (by omega) a b
  have := PMFFT.polyMulPrice_mono p (clog2_mono (show 2 * k - 1 ≤ 2 * N by omega))
  unfold fftLB
  unfold PMFFT.karMax at *
  omega

theorem invBound_fft (hP : Includes P inverseModXFFTC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) (N : ℕ) (hN : N ≤ 2 ^ 35) : InvBound P N (fftIB p N) := by
  intro k a hk
  have := PMFFT.inverseModXFFTC_cost P hP p hp k (by omega) a
  have := PMFFT.newtonBound_mono p hk
  unfold fftIB
  omega

/-- **The PM-basis core at the leaf's proved price** (`pmCoreC_cost` and
`leafCost`): the tree at the leaf price `leafBound r m + 21·m + 32`. -/
theorem pmCoreCostAt_leaf (hP : Includes P pmCoreC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) {r m SB : ℕ} (hr : 2 ≤ r) (hm : m ≤ r) (hr28 : r < 2 ^ 28)
    (hSB : SB < 2 ^ 39) :
    PMCoreCostAt P p (PMCore.leafBound r m + 21 * m + 32) r m SB := fun problem shift hI ↦
  PMCore.pmCoreC_cost P hP hp hr hm (by omega) hSB
    (PMCore.leafCost P hP (r := r) (m := m) (SB := SB) hr28 (by omega) hSB) problem shift hI

/-- **The lanes' interpolation, compiled, within its proved price** (`interpolatePMC`): no
hypothesis but the shape's (`PMInterpOK`, decidable) and the chain's `InterpSizes`. -/
theorem interpolatePMC_cost_model (hP : Includes P interpolatePMC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) (points : Array (K × K)) (params : GuruswamiSudan.GSInterpParams)
    (hok : PMInterpOK points.size params) (hsz : InterpSizes points.size params)
    (hk : 1 < params.messageDegree) :
    machineCost P interpolatePMC.costIdx [encodeValue points, encodeValue params] ≤
      interpPMModel p points.size params := by
  obtain ⟨hpm, hN35, hSB, h37⟩ := hok
  have hpm' := hpm
  obtain ⟨hn1, hm1, hmw, hw20, hN45, hW40⟩ := hpm'
  have hmn : params.multiplicity * points.size ≤ (params.multiplicity + 1) * points.size := by
    have := Nat.mul_le_mul_right points.size (show params.multiplicity ≤ params.multiplicity + 1
      by omega)
    omega
  have hn : points.size ≤ (params.multiplicity + 1) * points.size := by
    have := Nat.mul_le_mul_right points.size (show 1 ≤ params.multiplicity + 1 by omega)
    omega
  exact interpolatePMC_cost P (by includes) p points params
    (mulBound_fft P (by includes) p hp _ (by omega))
    (lowBound_fft P (by includes) p hp _ (by omega))
    (lowBound_fft P (by includes) p hp _ (by omega))
    (invBound_fft P (by includes) p hp _ (by omega))
    (pmCoreCostAt_leaf P (by includes) p hp (by omega) (by omega) (by omega) hSB)
    (by omega) h37 hsz hpm hk

/-- **The lanes' interpolation within the model's price** (`interpPMPrice`, `PMBasis`), on the
shapes where the proved price is within it (`interpPMModel p n params ≤ interpPMPrice p n params`,
decidable, checked per shape). -/
theorem interpolatePMC_cost_price (hP : Includes P interpolatePMC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) (points : Array (K × K)) (params : GuruswamiSudan.GSInterpParams)
    (hok : PMInterpOK points.size params)
    (hle : interpPMModel p points.size params ≤ interpPMPrice p points.size params)
    (hsz : InterpSizes points.size params) (hk : 1 < params.messageDegree) :
    machineCost P interpolatePMC.costIdx [encodeValue points, encodeValue params] ≤
      interpPMPrice p points.size params :=
  (interpolatePMC_cost_model P hP p hp points params hok hsz hk).trans hle

end

end LeanVM.Cost.Bounds.PMSolve
