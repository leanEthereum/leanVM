module

public import LeanVM.Cost.Bounds.PMBasis.Defs
public import LeanVM.Cost.Bounds.Decoder.ShapeDefs

/-!
# The lane decoder on `pmSolver`: the price model

The decoder `decodeStacksDistinctPM` (`Fast/LanePM.lean`) is the extractor's decoder
(`decodeStacksDistinct`) with each lane interpolated by the approximant-basis interpolation on the
non-adaptive solver `pmSolver` (`interpolateDistinctWith pmSolver`). Its price, the
interpolation's part `interpPMPrice`, the rest the bounds of `Bounds/Decoder/ShapeDefs.lean`
(proved of the compiled chain):

* **the interpolation** (`interpPMPrice`), `n` points, multiplicity `m`, `w = ℓ + 1` columns,
  weighted degree `W`:
  - `G` and `R` (`vanishingFast`, `interpolateCoefficientFormWithVanishing` by Horner):
    `362·n² + 309·(n+1)·n + 4146·n + 299` (`vanishingC_cost`, `interpolateC_cost`);
  - the GS data (`buildGSModularDataWithRG`, `gsDataPrice`): the `m` moduli `G^(m−b)` by `m − 1`
    products, the relation matrix's `m` columns by at most `m·w` multiply-reduce steps
    (`gsRelationColumn`), every product and remainder at the largest size `(m + 1)·n + 1`
    (model: a product `polyMulPrice`, a remainder `polyModPrice` = five products: Newton's
    inverse at full precision, the quotient, the back-product), the entries scaled by their
    binomials, the matrix assembled;
  - the certified solve (`certifiedSolutionBasis`, `certSolvePrice`): the lift (`(w + m)·m`
    entries of at most `m·n + 1` coefficients copied, the first branch of each remainder), the
    PM-basis on `w + m` rows, `m` columns, maximal order `m·n + W + 2` (`pmBasisPrice`,
    `gsProblem_maxOrder`), the certified rows' degree reads and principal parts;
  - the least row (`leastShiftedDegreeChoice?`) and the normalization (`normBound`, existing, and
    the row as a bivariate polynomial);
* **the rest of the lane's run** (`gsRunBoundPM`): the truncation, Roth–Ruckenstein's search
  (`rrBound`, `≈ 2^74.91` per lane at `(28, 4)`, evaluated in `LeanVMTests/Cost/RrBound.lean`), the candidates' filter;
* **the lane and the decoder** (`decoderLaneRunBoundPM`, `decoderLaneBoundPM`, `decoderBoundPM`),
  on `gsRunBoundPM`: the parameter search, the lane's points, its candidates encoded (`laneExtraBound`), the `64` lanes pruned
  (`pruneBound`), a stack per survivor.

Everything but the interpolation is an existing bound proved of the compiled chain; the
interpolation's parts are the model, in `PMPrices`.

**What turns the model into a bound** (price facts of the compiled functions, each for every
program including their bodies, at a `PMPrices` `p`):

1. the PM-basis core (`pmBasisWithFuelCore` on the target runtime): its `costEq` at fuel `0` and
   `fuel + 1`; a leaf (`popovLeafBasis`, order `≤ 1`, `r` rows) at most `pmLeafPrice p r`; a
   node's own price at most `pmNodePrice p r m o` from `popovRuntime_core_node`'s facts, i.e.
   `mulEvalP`/`mulTruncEvalP` at most `evalMatPrice` (`planFwd` and the conversion to the novel
   basis within `fwdPrice`, `planInv` and the conversion back within `invPrice`, `evalDot` within
   `mac` per multiply-add, `mkPlan` within `2^20`, the transform within `maxLog`), and `maxOrder`,
   `lowerOrders`, `residualOrders`, `divXTrunc`, `updateShiftByRows`, `compactNonzeroRows`
   within `ovh·r·(2r + m)·(o + 1) + 2^20`; then `pmBasisFuel_price_le` gives `pmTree`;
2. `fftMulContext`'s product within `polyMulPrice p (clog2 (deg + deg + 1))`, `fftModContext`'s
   remainder within `polyModPrice`, a scaling within `coeff` per coefficient; hence `gsModuli`,
   `gsRelationColumn`, `gsRelationMatrixWithModuli` within `gsDataPrice`;
3. `certifiedGuard`, `fullWindowExactNullspaceProblem` (each lift remainder on its first branch,
   `ovh` per coefficient), `exactNullspaceShift`, the `certifiedRow` filter and
   `principalSolutionRows` within `certSolvePrice` less the PM-basis;
4. `leastShiftedDegreeChoice?` within `ovh·r·w + 64·r + 100`, `normalizeLeeFast` within
   `normBound`, `CBivariate.ofCoeffRow` within `ovh·w·(W + 2)`; `vanishingFast` and the Horner
   interpolation as proved (`vanishingC_cost`, `interpolateC_cost`), if compiled as before;
5. `interpolateDistinctWith pmSolver`'s glue within `2^20`; then `gsRunDistinctWith` as
   `gsRunDistinctNFC_cost` (`prefixesNFC_cost`, `truncateXC_cost`, the filter) with the
   interpolation swapped, and the lane, the pruning and the stacks as `decoderLaneC_cost`,
   `pruneUpToDistinctC_cost` (generic in a lane's price) and `decodeStacksDistinctC_cost`.
-/

namespace LeanVM.Cost.Bounds.PMBasis

open LeanVM.Parameters LeanVM.Extraction CompPoly CompPoly.GuruswamiSudan
open LeanVM.Cost.Bounds.Decoder

public section

/-- **One polynomial product over `2^j` points** (`FFT.fftMulContext`'s transform branch): two
forward transforms, `2^j` pointwise multiply-adds, one inverse, the plan. -/
@[expose] def polyMulPrice (p : PMPrices) (j : ℕ) : ℕ :=
  2 * fwdPrice p j + invPrice p j + p.mac * 2 ^ j + 2 ^ 20

/-- **One remainder modulo a monic polynomial, operands within `2^j` coefficients** (model;
`FFT.fftModContext`): five products of size `2^j` (Newton's inverse of the reversed modulus at
full precision about three, the quotient, the back-product). -/
@[expose] def polyModPrice (p : PMPrices) (j : ℕ) : ℕ := 5 * polyMulPrice p j

/-- **`G` and `R`**: the chain's vanishing polynomial and Horner interpolation on `n` points
(`vanishingC_cost`, `interpolateC_cost`). -/
@[expose] def grPrice (n : ℕ) : ℕ := 362 * (n * n) + 309 * ((n + 1) * n) + 4146 * n + 299

/-- **The GS modular data** (`buildGSModularDataWithRG`), `n` points, multiplicity `m`, `w`
columns: `m` products for the moduli, `m` reductions of `R`, at most `m·w` multiply-reduce steps
of the relation columns with their binomial scalings, the matrix assembled; every size at most
`(m + 1)·n + 1` coefficients. -/
@[expose] def gsDataPrice (p : PMPrices) (n m w : ℕ) : ℕ :=
  m * polyMulPrice p (clog2 ((m + 1) * n + 1)) + m * polyModPrice p (clog2 ((m + 1) * n + 1)) +
    m * w * (polyMulPrice p (clog2 ((m + 1) * n + 1)) + polyModPrice p (clog2 ((m + 1) * n + 1)) +
      (p.coeff + p.ovh) * ((m + 1) * n + 1)) +
    p.ovh * (w * m * (m * n + 1))

/-- **The certified solve** (`certifiedSolutionBasis` at `W`): the lift's `(w + m)·m` entries
copied, the orders, the PM-basis (`pmBasisPrice`, `w + m` rows, `m` columns, maximal order
`m·n + W + 2`), each basis row's size and shifted degree read, the principal parts. -/
@[expose] def certSolvePrice (p : PMPrices) (n m w W : ℕ) : ℕ :=
  p.ovh * ((w + m) * m * (m * n + 1)) + p.ovh * m +
    pmBasisPrice p (w + m) m (m * n + W + 2) + p.ovh * ((w + m) * (w + m)) +
    p.ovh * ((w + m) * w)

/-- **The interpolation on `pmSolver`** (`interpolateDistinctWith pmSolver`), `n` points:
`G` and `R`, the GS data, the certified solve, the least row (a degree read per entry), the
normalization (`normBound`, and the row read as a bivariate polynomial), `2^41` of glue (the
model's margin at the smallest shapes). -/
@[expose] def interpPMPrice (p : PMPrices) (n : ℕ) (params : GSInterpParams) : ℕ :=
  grPrice n + gsDataPrice p n params.multiplicity (interpolationWidth params) +
    certSolvePrice p n params.multiplicity (interpolationWidth params)
      params.weightedDegreeBound +
    (p.ovh * ((interpolationWidth params + params.multiplicity) * interpolationWidth params) +
      64 * (interpolationWidth params + params.multiplicity) + 100) +
    normBound params.weightedDegreeBound (interpolationWidth params) +
    p.ovh * (interpolationWidth params * (params.weightedDegreeBound + 2)) + 2 ^ 41

/-- **One lane's run on `pmSolver`** (`gsRunDistinctWith pmSolver`): the interpolation
`interpPMPrice`, the truncation, Roth–Ruckenstein's search (`rrBound`), the candidates' filter. -/
@[expose] def gsRunBoundPM (p : PMPrices) (n : ℕ) (params : GSInterpParams) : ℕ :=
  interpPMPrice p n params + 10 +
    ((25 * (params.weightedDegreeBound + 1) + 72) * (interpolationYCap params + 1) + 25) +
    rrBound (params.weightedDegreeBound + 1) (interpolationYCap params + 2) params.messageDegree
      (interpolationYCap params) +
    ((46 * params.messageDegree + 36) * n + 54) * max 1 (interpolationYCap params) + 40

/-- **A lane's run on `pmSolver`** (`gsLaneWith pmSolver κ R A`): the parameter search, the
lane's `n = 2^(κ+R)` points (`BS` per symbol), the run (`gsRunBoundPM`). -/
@[expose] def decoderLaneRunBoundPM (p : PMPrices) (κ R A BS : ℕ) : ℕ :=
  138 * gsMultiplicityBoundAt (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A + (BS + 30) * 2 ^ (κ + R) +
    gsRunBoundPM p (2 ^ (κ + R)) (gsParamsFor (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A).interp + 136

/-- **A lane's candidates on `pmSolver`** (`laneEncodedWith pmSolver κ R A`): the run, then at
most `max 1 ℓ` candidates of at most `2^κ + 6` coefficients (`laneExtraBound`). -/
@[expose] def decoderLaneBoundPM (p : PMPrices) (κ R A BS : ℕ) : ℕ :=
  decoderLaneRunBoundPM p κ R A BS +
    laneExtraBound κ R (max 1 (interpolationYCap (gsParamsFor (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A).interp))
      (2 ^ κ + Whir.initialFold)

/-- **The decoder on `pmSolver`** (`decodeStacksDistinctPM μ R`) at the shape `(μ, R)`
(`κ = μ − 6`, `n = 2^(κ+R)`, the Johnson threshold `A`): the `2^6` lanes pruned (`pruneBound`: the
word's table, `BW` per column and `Lw` symbols per column; a lane `decoderLaneBoundPM`, at most
`max 1 ℓ` candidates, at most `2^12` survivors), a stack per survivor. -/
@[expose] def decoderBoundPM (p : PMPrices) (μ R BW Lw : ℕ) : ℕ :=
  pruneBound (μ - Whir.initialFold) R (2 ^ Whir.initialFold) BW Lw
      (decoderLaneBoundPM p (μ - Whir.initialFold) R (johnsonThreshold μ R) 13)
      (max 1 (interpolationYCap (gsParamsFor (2 ^ (μ - Whir.initialFold) + Whir.initialFold)
        (2 ^ (μ - Whir.initialFold + R)) (johnsonThreshold μ R)).interp))
      (2 ^ 12) +
    ((15 * 2 ^ Whir.initialFold + 48) * 2 ^ μ + 34) * 2 ^ 12 + 14132

end

end LeanVM.Cost.Bounds.PMBasis
