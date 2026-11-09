module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# PM-basis's price: the definitions

The price of CompPoly's divide-and-conquer approximant basis (`pmBasisWithFuelCore`,
`CompPoly/LinearAlgebra/PolynomialMatrix/Approximant/PMBasis/Recursion.lean:82`) as a function of
the problem's maximal order, for a node price `N` and a leaf price `L` given as functions, and the
per-operation price model the compiled code's bounds are stated in. Here, apart from their proofs
(`Bounds/PMBasis/Tree.lean`, `Recursion.lean`), so that the shape checks
(`Bounds/PMLane/Shapes.lean`) import only what they evaluate.

* `pmTree c L N o`: the recursion's own tree on the maximal order `o`: a leaf (`o ≤ c` or
  `o ≤ 1`) at `L`, else `N o` and the two halves `⌊o/2⌋` (the lower orders) and `o − ⌊o/2⌋`
  (the residual orders), as `pmBasisWithFuelCore` splits;
* `pmTreePair c L N f q = (pmTree q, pmTree (q + 1))`, its evaluation in `f` steps (the orders at a
  depth are two consecutive numbers), for kernel evaluation (`pmTreePair_eq`);
* the price model of the FFT-based recursion (`PMPrices`, `evalMatPrice`, `pmNodePrice`,
  `pmLeafPrice`, `pmBasisPrice`), in per-operation prices (`PMPrices`; the compiled pieces' proved
  prices fit them at `marginPrices`, `Bounds/PMBasis/Values.lean`).
-/

namespace LeanVM.Cost.Bounds.PMBasis

public section

/-- The search for the least `j ≥ j₀` with `e ≤ 2^j`, in `fuel` steps: `ceilLogLoop` of
`Fast/EvalMat/Product.lean`, copied so that this file imports no product (`clog2_eq_ceilLog`). -/
@[expose] def clog2Loop (e : ℕ) : ℕ → ℕ → ℕ
  | 0, j => j
  | fuel + 1, j => if e ≤ 2 ^ j then j else clog2Loop e fuel (j + 1)

/-- `⌈log₂ e⌉`, the least `j` with `e ≤ 2^j`: the transform size's exponent `ceilLog` of
`mulEval`/`mulTruncEval` (`Fast/EvalMat/Product.lean`; `clog2_eq_ceilLog`). -/
@[expose] def clog2 (e : ℕ) : ℕ := clog2Loop e e 0

/-! ## The recursion's tree -/

/-- **The divide-and-conquer tree on the maximal order** `o`, a leaf at most `c` (the leaf
cutoff) or at most `1` costing `L`, an inner node `N o` and its two children at the lower half
`o / 2` and the residual half `o − o / 2` (`pmBasisWithFuelCore`'s `d₁ := order / 2`,
`lowerOrders`, `residualOrders`). -/
@[expose] def pmTree (c L : ℕ) (N : ℕ → ℕ) (o : ℕ) : ℕ :=
  if o ≤ c ∨ o ≤ 1 then L else N o + pmTree c L N (o / 2) + pmTree c L N (o - o / 2)
termination_by o
decreasing_by all_goals omega

/-- One node of `pmTree` from its children's two possible values: at `x ∈ {q, q + 1}`, children
in `{h, h + 1}`, `h = q / 2`, priced `a` and `b`. -/
@[expose] def pmTreeStep (c L : ℕ) (N : ℕ → ℕ) (h a b x : ℕ) : ℕ :=
  if x ≤ c ∨ x ≤ 1 then L
  else N x + (if x / 2 = h then a else b) + (if x - x / 2 = h then a else b)

/-- `(pmTree q, pmTree (q + 1))` in `f` halvings (`q + 1 ≤ 2^f`): the orders at one depth of the
tree are two consecutive numbers, so the tree is evaluated in `log₂ q` steps. -/
@[expose] def pmTreePair (c L : ℕ) (N : ℕ → ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (L, L)
  | f + 1, q =>
    let ab := pmTreePair c L N f (q / 2)
    (pmTreeStep c L N (q / 2) ab.1 ab.2 q, pmTreeStep c L N (q / 2) ab.1 ab.2 (q + 1))

/-- `pmTree` by `pmTreePair` in `clog2 (o + 1)` halvings (`pmTreeEval_eq`): kernel-evaluable. -/
@[expose] def pmTreeEval (c L : ℕ) (N : ℕ → ℕ) (o : ℕ) : ℕ :=
  (pmTreePair c L N (clog2 (o + 1)) o).1

/-! ## The price model -/

/-- **The prices of the model's operations**, in steps of the cost machine (`marginPrices`,
`Values.lean`). -/
structure PMPrices where
  /-- A pointwise multiply-add of the evaluation-domain product (`evalDot`). -/
  mac : ℕ
  /-- A forward NTT stage, per element (`fwdStageFast` with the plan's twiddles). -/
  fwd : ℕ
  /-- An inverse NTT stage, per element (`invStageFast`). -/
  inv : ℕ
  /-- The conversion monomial → novel basis, per `j·2^j` (`Fast/FFT/Convert.lean`). -/
  toNovel : ℕ
  /-- The conversion novel → monomial basis, per `j·2^j` (`Fast/FFT/Convert.lean`). -/
  fromNovel : ℕ
  /-- The order-one leaf (`popovLeafBasis`), per `r³`. -/
  leafCube : ℕ
  /-- The order-one leaf, per `r²`. -/
  leafSquare : ℕ
  /-- A coefficient product of the schoolbook product (sums and products trimmed once). -/
  coeff : ℕ
  /-- A coefficient copied, padded, truncated or a degree read. -/
  ovh : ℕ

/-- **The forward transform of one entry over `2^j` points**: the conversion to the novel basis
and `j` forward stages, the entry padded. -/
@[expose] def fwdPrice (p : PMPrices) (j : ℕ) : ℕ :=
  (p.toNovel + p.fwd) * (j * 2 ^ j) + p.ovh * 2 ^ j

/-- **The inverse transform of one entry over `2^j` points**: `j` inverse stages and the
conversion back to the monomial basis, the entry trimmed. -/
@[expose] def invPrice (p : PMPrices) (j : ℕ) : ℕ :=
  (p.fromNovel + p.inv) * (j * 2 ^ j) + p.ovh * 2 ^ j

/-- **An evaluation-domain matrix product** (`mulEvalP`/`mulTruncEvalP`): `R × S` of degree
`≤ dA` by `S × T` of degree `≤ dB` over `2^j` points, `j = clog2 (dA + dB + 1)` (`mulEval`'s
`ceilLog`, the doubling at exact powers of two): `(R·S + S·T)` forward transforms, `R·T` inverse
ones, `R·S·T·2^j` pointwise multiply-adds, and `2^20` for the plan (`mkPlan j`: `O(j²)` products
and one inversion, `j ≤ 64`). -/
@[expose] def evalMatPrice (p : PMPrices) (R S T dA dB : ℕ) : ℕ :=
  (R * S + S * T) * fwdPrice p (clog2 (dA + dB + 1)) +
    R * T * invPrice p (clog2 (dA + dB + 1)) +
    R * S * T * 2 ^ clog2 (dA + dB + 1) * p.mac + 2 ^ 20

/-- **An inner node's own price** (model), at maximal order `o`, `d₁ = o / 2`, `r` rows, `m`
columns, the degree ≤ order invariant (`popovRuntime_core_node`): the composition `P₂·P₁`
(`r × r` of degree `≤ o − d₁` by `r × r` of degree `≤ d₁`), the residual product `P₁·A`
(`r × r` of degree `≤ d₁` by `r × m` truncated to degree `< o`), and `ovh` per coefficient of the
node's matrices read or written besides (the residual's `divXTrunc`, the shift update, the row
compaction, the residual product's truncation of its `r² + 2·r·m` entries at the order), `2^20` per
node for the rest (orders, folds). -/
@[expose] def pmNodePrice (p : PMPrices) (r m o : ℕ) : ℕ :=
  evalMatPrice p r r r (o - o / 2) (o / 2) + evalMatPrice p r r m (o / 2) (o - 1) +
    p.ovh * (r * (2 * r + 4 * m) * (o + 1)) + 2 ^ 20

/-- **A leaf's price** (model): an order-one leaf of `r` rows. -/
@[expose] def pmLeafPrice (p : PMPrices) (r : ℕ) : ℕ := p.leafCube * r ^ 3 + p.leafSquare * r ^ 2

/-- **PM-basis's whole price** (model) on the target runtime (`popovRuntime`, cutoff `1`; its
`pmBasis` is its core at `pmBasisFuel`, no root pass: `pmBasis_popovRuntime_eq_core`): the fuel's
fold over the `m` orders and the recursion (`pmTree`). -/
@[expose] def pmBasisPrice (p : PMPrices) (r m o : ℕ) : ℕ :=
  (64 * m + 100) + pmTreeEval 1 (pmLeafPrice p r) (pmNodePrice p r m) o

end

end LeanVM.Cost.Bounds.PMBasis
