module

public import LeanVM.Protocol.Extraction.Extractor
public import Statement.CostMachine
public import LeanVM.Cost.Prices

/-!
# Bounds: the decoder's bounds, as definitions

The bounds the decoder's proofs (`Bounds/Decoder/*.lean`) establish, from Roth–Ruckenstein's
nodes and the roots in `K` up to a lane's extra work and the pruning (`pruneBound`), and the sizes
a lane's bound needs (`DecoderLaneSizes`); the decoder's bound on the approximant-basis
interpolation assembles them (`decoderBoundPM`, `Bounds/PMBasis/LaneDefs.lean`). They are here,
apart from their proofs, so that the checks evaluating them (`Bounds/PMLane/Shapes.lean`) import
only what they evaluate (the extractor's parameter search and these numbers): an edit of a proof
rebuilds no check (`Bounds/PMLane/ShapesFirewall.lean` guards it).
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Parameters CompPoly CompPoly.GuruswamiSudan LeanVM.Extraction

public section

/-- The bound of `L` levels of the butterfly Taylor shift on at most `Y` rows of at most `X`
coefficients: per level a power by squaring and `Y` entries, each at most a scaled sum of rows. -/
@[expose] def bfLoopBound (X Y L : ℕ) : ℕ :=
  L * ((100 * X + 121) * Y + 73 * (Nat.log2 Y + 1) + 47) + 14

/-- The bound of the substitution on `Y` rows of at most `X` coefficients: the butterfly's
`log₂ Y + 1` levels, then each row shifted. -/
@[expose] def substBound (X Y : ℕ) : ℕ :=
  bfLoopBound X Y (Nat.log2 Y + 1) + (26 * (X + Y) + 78) * Y + 39

/-- The bound of a product modulo `u`, operands and `u` of at most `B` coefficients. -/
@[expose] def mulModBound (B : ℕ) : ℕ := 582 * (B * B) + 430 * B + 2960

/-- The bound of a remainder, operands of at most `B` coefficients. -/
@[expose] def rawModBound (B : ℕ) : ℕ := 117 * (B * B) + 326 * B + 6110

/-- The bound of a monic gcd's step, operands of at most `B` coefficients. -/
@[expose] def gcdStepBound (B : ℕ) : ℕ := rawModBound B + 45 * B + 54

/-- The bound of a monic gcd, operands of at most `B` coefficients. -/
@[expose] def gcdBound (B : ℕ) : ℕ := gcdStepBound B * (2 * B + 1) + 158 * B + 2962

/-- The bound of `k` Frobenius powers modulo `u`, `u` of at most `B` coefficients. -/
@[expose] def frobBound (B k : ℕ) : ℕ := (2 * mulModBound B + 21 * B + 57) * k + 116 * B + 3163

/-- The bound of the trace polynomial over `64` powers of at most `B` coefficients. -/
@[expose] def traceBound (B : ℕ) : ℕ := (154 * B + 421) * 64 + 982

/-- The bound of one base constant's child. -/
@[expose] def refineLamBound (B : ℕ) : ℕ := gcdBound B + 187 * B + 3092

/-- The bound of one factor's refinement, the factor of at most `B` coefficients, the cache of at
most `L` entries of at most `C` coefficients. -/
@[expose] def refineFactorBound (B C L : ℕ) : ℕ :=
  134 * B + 2728 + (18 * B + 3 * C + 24) * L + frobBound B 64 + traceBound B +
    2 * (refineLamBound B + 13) + 300

/-- The slope of a factor's refinement in its size, factors of at most `B` coefficients:
`refineFactorBound b C L ≤ b·refineSlope B + 441107 + (18·b + 3·C + 24)·L` for `b ≤ B`. -/
@[expose] def refineSlope (B : ℕ) : ℕ := 468 * (B * B) + 76214 * B + 92578

/-- The bound of one trace coordinate over the factors (`refineFactorsFast`), at most `F` factors
of at most `B` coefficients, their sizes summing to at most `S`, the cache of at most `L`
entries: each factor priced at its own size. -/
@[expose] def refineFactorsBound (B S F L : ℕ) : ℕ :=
  S * refineSlope B + (441107 + 2 * F + 33) * F + 18 * S * L + (3 * B + 24) * F * L + 15

/-- The bound of the splitter on a polynomial of at most `B` coefficients: `64` trace
coordinates, each over factors of sizes summing to at most `2·B`, at most `B` of them, the cache
of at most `64·B` entries. -/
@[expose] def splitBound (B : ℕ) : ℕ :=
  64 * (refineFactorsBound B (2 * B) B (64 * B) + 19) + 134 * B + 4586

/-- The bound of the root product, `p` of at most `B` coefficients. -/
@[expose] def rootProductBound (B : ℕ) : ℕ :=
  gcdBound B + 419 * B + 9728 + (2 * mulModBound B + 41) * 65

/-- **The roots of `F` linear factors**, validated against `p` (of at most `B` coefficients),
deduplicated: at most `rootsFromBound B F`. -/
@[expose] def rootsFromBound (B F : ℕ) : ℕ := (46 * B + 2940) * F + (19 * F + 31) * F + 32

/-- The bound of the roots in `K` of a polynomial of at most `B` coefficients. -/
@[expose] def rootsBound (B : ℕ) : ℕ :=
  3 * B + 54 + rootsFromBound B 1 + rootProductBound B + splitBound B + (B + 33) * B + 3 * B +
    9 + rootsFromBound B B

/-- The price of a node of `Y` rows of at most `X` coefficients, beyond its children: the
`X`-adic order, the division by `X^s`, the initial coefficient polynomial, its roots. -/
@[expose] def rrNodePrice (X Y : ℕ) : ℕ :=
  (63 * X + 188) * Y + rootsBound Y + 125

/-- The price of a child in its parent's fold, `k` the depth bound: the substitution, the
truncation, the prefix extended. -/
@[expose] def rrChildPrice (X Y k : ℕ) : ℕ :=
  substBound X Y + (25 * (X + Y) + 72) * Y + 108 * k + 202

/-- The bound of Roth–Ruckenstein's search on `1 + k·ℓ` nodes of `Y` rows of at most `X`
coefficients, `k` levels. -/
@[expose] def rrBound (X Y k ℓ : ℕ) : ℕ :=
  (rrNodePrice X Y + rrChildPrice X Y k + Y * k) * (1 + k * ℓ)

/-- The bound of the normalization on `rows` rows. -/
@[expose] def normBound (W rows : ℕ) : ℕ :=
  (2953 * (W + 1) + 221) * rows + 119

/-- The sizes the interpolation's bound needs, all word-sized. -/
@[expose] def InterpSizes (n : ℕ) (params : GSInterpParams) : Prop :=
  n < 2 ^ 55 ∧ params.weightedDegreeBound + 1 < 2 ^ 60 ∧ params.messageDegree < 2 ^ 64 ∧
    yWeight params * (params.weightedDegreeBound + 1) < 2 ^ 64 ∧
    interpolationYCap params + 1 < 2 ^ 55 ∧ params.multiplicity < 2 ^ 55 ∧
    (params.multiplicity + 1) * n + 2 < 2 ^ 55 ∧
    2 * (params.multiplicity * n + interpolationYCap params * yWeight params + 1) +
      interpolationYCap params * yWeight params < 2 ^ 62 ∧
    (interpolationYCap params + 2) * (interpolationYCap params + 2) *
      (params.multiplicity * n + interpolationYCap params * yWeight params +
        interpolationYCap params * yWeight params + 2) < 2 ^ 64

/-- The price of one lane beyond its Guruswami–Sudan run: at most `L` candidates of at most `k`
coefficients, `N = 2^κ`, `M = 2^(κ+R)`. -/
@[expose] def laneExtraBound (κ R L k : ℕ) : ℕ :=
  ((46 * k + 34) * 2 ^ κ + κ * (174 * 2 ^ κ + 2921) + 51) * L +
    ((21 * 2 ^ κ + 26) * L + 25) * L + (53 * 2 ^ κ + 95) * (L * L) +
    (κ * (171 * 2 ^ (κ + R) + 2924) + 28 * 2 ^ (κ + R) + 60) * L + 44

/-- The bound of the pruning over `U` lanes of `n = 2^(κ+R)` columns: the word's table (a column
price `BW`, columns of at most `Lw` symbols), per lane its candidates (`G`) and the pruning step
(`Smax` survivors, `Lc` candidates). -/
@[expose] def pruneBound (κ R U BW Lw G Lc Smax : ℕ) : ℕ :=
  (BW + 12 * Lw + 28) * 2 ^ (κ + R) + 16 * 2 ^ (κ + R) +
    (G + Smax * (Lc * (48 * 2 ^ (κ + R) + 11 * U + 71) + 39) + 53) * U + 15 * U + 62

/-- The sizes at which a lane is bounded: word-sized parameters (`InterpSizes`, …), `k > 1`, at
most `2^20` multiplicities tried. -/
@[expose] def DecoderLaneSizes (κ R A : ℕ) : Prop :=
  κ + R ≤ 30 ∧ A ≤ 2 ^ (κ + R) ∧ gsMultiplicityBoundAt (2 ^ κ) (2 ^ (κ + R)) A < 2 ^ 20 ∧
    InterpSizes (2 ^ (κ + R)) (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp ∧
    1 < (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.messageDegree ∧
    (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.weightedDegreeBound + 1 < 2 ^ 56 ∧
    interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp + 2 < 2 ^ 28

instance (κ R A : ℕ) : Decidable (DecoderLaneSizes κ R A) := by
  unfold DecoderLaneSizes InterpSizes; infer_instance

end

end LeanVM.Cost.Bounds.Decoder
