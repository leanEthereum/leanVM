module

public import LeanVM.Cost.Bounds.PMBasis.Tree
public import LeanVM.Protocol.Extraction.Fast.EvalMat.Product
public import LeanVM.Protocol.Extraction.Fast.PMBasis.DegreeRecursion
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Recursion

/-!
# PM-basis's price on CompPoly's recursion

CompPoly's driver `pmBasisWithFuelCore rt` (`Approximant/PMBasis/Recursion.lean:82`), on any
runtime `rt` (the target, `popovRuntime mulCtx lowCtx 1 c` of `Fast/PMBasis/PopovCore.lean`,
among them): at fuel `0`, or at a maximal order `o ≤ rt.leafCutoff` or `o ≤ 1`, the leaf;
otherwise, with `d₁ = o / 2`, `P₁` on the lower orders `min oⱼ d₁` (`pmLower`), the residual
problem on the orders `oⱼ − d₁` and the matrix `(P₁·A) div X^d₁` (`pmResidual`), `P₂` on it under
the shift `updateShiftByRows P₁ shift` (`pmShifted`), and `compactNonzeroRows (P₂·P₁)`.

**`pmBasisWithFuelCore_price_le`**: a price `T fuel problem shift` (the compiled core's
`machineCost`, once compiled) with

* a leaf (maximal order `≤ rt.leafCutoff` or `≤ 1`) at most `L`;
* a node (maximal order `o ≥ 2`, `> rt.leafCutoff`, `o ≤ fuel + 2`) at most `N o` and its two
  children's prices `T fuel (pmLower problem) shift` and
  `T fuel (pmResidual rt fuel problem shift) (pmShifted rt fuel problem shift)`, the invariant
  `Inv` passed to both,

is at most `pmTree rt.leafCutoff L N (maxOrder problem)` wherever `maxOrder problem ≤ fuel + 1`
(CompPoly's `pmBasisFuel = maxOrder + 1` among them: **`pmBasisFuel_price_le`**). The children's maximal
orders are exactly `d₁` and `o − d₁` (`maxOrder_pmLower`, `maxOrder_pmResidual`), so no
monotonicity of `N` is needed.

The node's hypotheses are what `popovRuntime_core_node` (`Fast/PMBasis/DegreeRecursion.lean`)
gives: `P₁`, `R`, `P₂` of exactly `m` rows, `P₁` of degree `≤ d₁`, `P₂` of degree `≤ o − d₁`, the
residual's entry `(i, j)` of at most `oⱼ − d₁` coefficients. With them the evaluation-domain
products' transform sizes are at most the model's (**`clog2_eq_ceilLog`**: the model's exponent is
`mulEval`'s `ceilLog`): the composition at `2^clog2 (o + 1)`, the residual's
truncated product at `2^clog2 (d₁ + o)`.
-/

namespace LeanVM.Cost.Bounds.PMBasis

open CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

/-! ## The model's transform size is `mulEval`'s -/

theorem clog2Loop_eq_ceilLogLoop (e : ℕ) :
    ∀ fuel j, clog2Loop e fuel j = LeanVM.Extraction.Fast.EvalMat.ceilLogLoop e fuel j
  | 0, _ => rfl
  | fuel + 1, j => by
    rw [clog2Loop, LeanVM.Extraction.Fast.EvalMat.ceilLogLoop, clog2Loop_eq_ceilLogLoop e fuel]

/-- **The model's exponent is the products'**: `clog2 = ceilLog` (`Fast/EvalMat/Product.lean`). -/
theorem clog2_eq_ceilLog (e : ℕ) : clog2 e = LeanVM.Extraction.Fast.EvalMat.ceilLog e :=
  clog2Loop_eq_ceilLogLoop e e 0

/-! ## The recursion's children -/

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The lower problem: the orders capped at `maxOrder / 2`, the same matrix. -/
@[expose] def pmLower (problem : XAdicProblem F) : XAdicProblem F :=
  { orders := lowerOrders problem (maxOrder problem / 2), matrix := problem.matrix }

/-- The residual problem: the orders less `maxOrder / 2`, the matrix `(P₁·A) div X^d₁` truncated
at them (`residualMatrixWithProduct`, by the runtime's residual product). -/
@[expose] def pmResidual (rt : PMBasisRuntime F) (fuel : ℕ) (problem : XAdicProblem F)
    (shift : Array ℕ) : XAdicProblem F :=
  { orders := residualOrders problem (maxOrder problem / 2)
    matrix := residualMatrixWithProduct rt.residualProduct
      (pmBasisWithFuelCore rt fuel (pmLower problem) shift) problem.matrix (maxOrder problem / 2)
      (residualOrders problem (maxOrder problem / 2)) }

/-- The residual's shift: `updateShiftByRows P₁ shift`. -/
@[expose] def pmShifted (rt : PMBasisRuntime F) (fuel : ℕ) (problem : XAdicProblem F)
    (shift : Array ℕ) : Array ℕ :=
  updateShiftByRows (pmBasisWithFuelCore rt fuel (pmLower problem) shift) shift

omit [BEq F] [LawfulBEq F] in
/-- The lower problem's maximal order is `⌊o/2⌋`. -/
theorem maxOrder_pmLower (problem : XAdicProblem F) :
    maxOrder (pmLower problem) = maxOrder problem / 2 := by
  have := LeanVM.Extraction.Fast.PMDegree.maxOrder_map (F := F) problem.orders
    (f := fun o ↦ min o (maxOrder problem / 2))
    (fun _ _ h ↦ min_le_min_right _ h) (Nat.zero_min _) problem.matrix
  rw [pmLower, lowerOrders, this]
  change min (maxOrder problem) _ = _
  omega

/-- The residual problem's maximal order is `o − ⌊o/2⌋`. -/
theorem maxOrder_pmResidual (rt : PMBasisRuntime F) (fuel : ℕ) (problem : XAdicProblem F)
    (shift : Array ℕ) :
    maxOrder (pmResidual rt fuel problem shift) = maxOrder problem - maxOrder problem / 2 :=
  LeanVM.Extraction.Fast.PMDegree.maxOrder_map problem.orders
    (f := fun o ↦ o - maxOrder problem / 2)
    (fun _ _ h ↦ Nat.sub_le_sub_right h _) (Nat.zero_sub _) _

/-! ## The price -/

/-- **PM-basis's recursion, priced**: a leaf at most `L`, a node at most `N o` and its two
children's prices (the invariant `Inv` passed to them), give at most
`pmTree rt.leafCutoff L N (maxOrder problem)` wherever `maxOrder problem ≤ fuel + 1`. -/
theorem pmBasisWithFuelCore_price_le (rt : PMBasisRuntime F)
    (T : ℕ → XAdicProblem F → Array ℕ → ℕ) (L : ℕ) (N : ℕ → ℕ)
    (Inv : XAdicProblem F → Array ℕ → Prop)
    (hleaf : ∀ fuel problem shift, Inv problem shift → maxOrder problem ≤ fuel + 1 →
      (maxOrder problem ≤ rt.leafCutoff ∨ maxOrder problem ≤ 1) → T fuel problem shift ≤ L)
    (hnode : ∀ fuel problem shift, Inv problem shift → maxOrder problem ≤ fuel + 2 →
      rt.leafCutoff < maxOrder problem → 2 ≤ maxOrder problem →
      Inv (pmLower problem) shift ∧
        Inv (pmResidual rt fuel problem shift) (pmShifted rt fuel problem shift) ∧
        T (fuel + 1) problem shift ≤ N (maxOrder problem) + T fuel (pmLower problem) shift +
          T fuel (pmResidual rt fuel problem shift) (pmShifted rt fuel problem shift)) :
    ∀ fuel problem shift, Inv problem shift → maxOrder problem ≤ fuel + 1 →
      T fuel problem shift ≤ pmTree rt.leafCutoff L N (maxOrder problem) := by
  intro fuel problem shift hI hf
  refine le_pmTree (α := ℕ × XAdicProblem F × Array ℕ)
    (fun x ↦ Inv x.2.1 x.2.2 ∧ maxOrder x.2.1 ≤ x.1 + 1) (fun x ↦ maxOrder x.2.1)
    (fun x ↦ T x.1 x.2.1 x.2.2) rt.leafCutoff L N
    (fun x hx hl ↦ hleaf x.1 x.2.1 x.2.2 hx.1 hx.2 hl) ?_ (fuel, problem, shift) ⟨hI, hf⟩
  rintro ⟨f, p, s⟩ ⟨hIx, hfx⟩ hc h1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp only at hfx h1; omega⟩
  simp only at hIx hfx hc h1 ⊢
  obtain ⟨hl, hr, hT⟩ := hnode f p s hIx (by omega) hc h1
  refine ⟨(f, pmLower p, s), (f, pmResidual rt f p s, pmShifted rt f p s), ⟨hl, ?_⟩, ⟨hr, ?_⟩,
    maxOrder_pmLower p, maxOrder_pmResidual rt f p s, hT⟩
  · simp only [maxOrder_pmLower]; omega
  · simp only [maxOrder_pmResidual]; omega

/-- **`pmBasis`'s core at CompPoly's fuel** (`pmBasisFuel = maxOrder + 1`; on the target runtime
`popovRuntime` this is `pmBasis` itself, `pmBasis_popovRuntime_eq_core`), priced. -/
theorem pmBasisFuel_price_le (rt : PMBasisRuntime F)
    (T : ℕ → XAdicProblem F → Array ℕ → ℕ) (L : ℕ) (N : ℕ → ℕ)
    (Inv : XAdicProblem F → Array ℕ → Prop)
    (hleaf : ∀ fuel problem shift, Inv problem shift → maxOrder problem ≤ fuel + 1 →
      (maxOrder problem ≤ rt.leafCutoff ∨ maxOrder problem ≤ 1) → T fuel problem shift ≤ L)
    (hnode : ∀ fuel problem shift, Inv problem shift → maxOrder problem ≤ fuel + 2 →
      rt.leafCutoff < maxOrder problem → 2 ≤ maxOrder problem →
      Inv (pmLower problem) shift ∧
        Inv (pmResidual rt fuel problem shift) (pmShifted rt fuel problem shift) ∧
        T (fuel + 1) problem shift ≤ N (maxOrder problem) + T fuel (pmLower problem) shift +
          T fuel (pmResidual rt fuel problem shift) (pmShifted rt fuel problem shift))
    (problem : XAdicProblem F) (shift : Array ℕ) (hI : Inv problem shift) :
    T (pmBasisFuel problem) problem shift ≤ pmTree rt.leafCutoff L N (maxOrder problem) :=
  pmBasisWithFuelCore_price_le rt T L N Inv hleaf hnode _ problem shift hI
    (by rw [pmBasisFuel]; omega)

end

end LeanVM.Cost.Bounds.PMBasis
