module

public import LeanVM.Cost.Bounds.PMFFT.Conv
public import LeanVM.Cost.Bounds.PMFFT.Stages
public import LeanVM.Cost.Bounds.PMFFT.PlanCost
public import LeanVM.Cost.Bounds.Decoder.Rows

/-!
# Bounds of the PM decoder's FFT: the polynomial transforms

`planFwdPoly` (monomial → novel, then the forward butterflies) and `planInvPoly` (the inverse
butterflies, novel → monomial, the result trimmed) by the plan of size `N = 2^j`, `j ≤ 40`.
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-- **The forward polynomial transform** (`planFwdPolyC`): at most
`29·N·j² + 230·N·j + 46·N + 231·j + 85`. -/
theorem planFwdPolyC_cost (hP : Includes P planFwdPolyC.costDeps) {j : ℕ} (hj : j ≤ 40)
    (f : CompPoly.CPolynomial K) :
    machineCost P planFwdPolyC.costIdx [encodeValue (FFT.mkPlan j), encodeValue f] ≤
      29 * (2 ^ j * (j * j)) + 230 * (2 ^ j * j) + 46 * 2 ^ j + 231 * j + 85 := by
  rw [planFwdPolyC.costEq P hP]
  have h1 := toNovelInPlaceC_cost P (by includes) hj f.val
  have h2 := planFwdC_cost P (by includes) hj (FFT.toNovelInPlace (FFT.mkPlan j) f.val)
  omega

theorem size_fromNovelInPlace_planInv {j : ℕ} (hj : j ≤ 64) (y : Array K) :
    (FFT.fromNovelInPlace (FFT.mkPlan j) (FFT.planInv (FFT.mkPlan j) y)).size = 2 ^ j := by
  rw [FFT.fromNovelInPlace_eq hj]; exact (FFT.fromNovel_spec hj _).1

/-- **The inverse polynomial transform** (`planInvPolyC`): at most
`37·N·j² + 167·N·j + 44·N + 156·j + 84`. -/
theorem planInvPolyC_cost (hP : Includes P planInvPolyC.costDeps) {j : ℕ} (hj : j ≤ 40)
    (y : Array K) :
    machineCost P planInvPolyC.costIdx [encodeValue (FFT.mkPlan j), encodeValue y] ≤
      37 * (2 ^ j * (j * j)) + 167 * (2 ^ j * j) + 44 * 2 ^ j + 156 * j + 84 := by
  rw [planInvPolyC.costEq P hP]
  have h1 := planInvC_cost P (by includes) hj y
  have h2 := fromNovelInPlaceC_cost P (by includes) hj (FFT.planInv (FFT.mkPlan j) y)
  have hN : 2 ^ j ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hj
  have h3 := Decoder.ofArray_cost P (by includes)
    (FFT.fromNovelInPlace (FFT.mkPlan j) (FFT.planInv (FFT.mkPlan j) y))
    (by rw [size_fromNovelInPlace_planInv (by omega)]; omega)
  rw [size_fromNovelInPlace_planInv (by omega)] at h3
  omega

end

end LeanVM.Cost.Bounds.PMFFT
