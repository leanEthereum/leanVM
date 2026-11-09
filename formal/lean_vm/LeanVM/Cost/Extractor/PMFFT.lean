module

public import LeanVM.Cost.Extractor.Replay
public import LeanVM.Cost.LoopLib
public import LeanVM.Protocol.Extraction.Fast.LanePM
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Raw.Modular
import all CompPoly.Univariate.Context
import all CompPoly.Data.Array.Lemmas
import all Init.Data.Array.Basic
import all LeanVM.Cost.FastLib

/-!
# The lanes' approximant-basis interpolation, compiled (stage 1): the additive-FFT product

The extractor's decoder (`decOf`, `decodeStacksDistinctPM`) in five stages on the chain, after the
replay and before the top (`Top.lean`): this module, `PMEval`, `PMCore`, `PMSolve`, `PMLane`.

The conversions monomial ↔ novel basis, level by level (`FFT.toNovelInPlace`,
`FFT.fromNovelInPlace`), the planned transforms' butterflies (`FFT.planFwd`, `FFT.planInv`), the
plan of size `2^j` (`FFT.mkPlan`), the polynomial transforms (`FFT.planFwdPoly`,
`FFT.planInvPoly`), the product by the transform (`FFT.mulVia`, the schedule's schoolbook and
Karatsuba products below it) and the
low products the remainders use (`FFT.rawMulLowVia`). Each a function of its own, compiled first
under its own name.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Extraction.Fast.FFT

public section

cost_enc LeanVM.Extraction.Fast.FFT.FFTPlan

cost_compile toNovelInPlaceC := FFT.toNovelInPlace

cost_compile fromNovelInPlaceC := FFT.fromNovelInPlace

cost_compile planFwdC := FFT.planFwd

cost_compile planInvC := FFT.planInv

cost_compile mkPlanC := FFT.mkPlan

cost_compile planFwdPolyC := FFT.planFwdPoly

cost_compile planInvPolyC := FFT.planInvPoly

-- `fftMulContext`'s product.
cost_compile mulViaFFTC := FFT.mulVia novelTransform fftSchedule

-- `fftRawMulLowContext`'s low product.
cost_compile rawMulLowFFTC := FFT.rawMulLowVia novelTransform fftSchedule

-- Newton's inverse modulo `X^k` on the low products.
cost_compile inverseModXFFTC := CompPoly.CPolynomial.Raw.inverseModX fftRawMulLowContext

-- `fftModContext`'s remainder (by reversal).
cost_compile modByMonicFFTC := CompPoly.CPolynomial.modByMonicByReversal fftRawMulLowContext

end

end LeanVM.Cost.Extractor
