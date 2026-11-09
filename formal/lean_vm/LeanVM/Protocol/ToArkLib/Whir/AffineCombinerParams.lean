/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerParams

  The interpolation parameters of the affine MCA error and the error's numerator, as decidable
  integer conditions. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerJohnson

/-!
# Interpolation parameters

Annex B of the leanVM specification (branch `f128`), `def:epsaff`, and the Rust that checks the
deployed parameters (`crates/pcs/src/whir_config/affine_mca.rs`: `interpolation_m`,
`interpolation_holds`, `hypotheses`, `affine_error_log2`, `combiner_within`). For integers
`1 ≤ d < A ≤ n` and positive `m, D, B`:

* `bigM d A m D = min(D, ⌊(m A - D - 1) / d⌋)` (`M`);
* `unknowns d A m D = Σ_{j ≤ M} (m A - D - d j)(D - j + 1)` and
  `equations n d A m D = n Σ_{s ≤ min(m - 1, M)} (m - s)(D - s + 1)`, the two sides of the
  interpolation inequality ([CYWZ26, preprint], Lemma 4.2), in natural numbers (truncated
  subtraction is the Annex's `max(0, ·)`; every summand on the left is positive for `j ≤ M`);
* `Admissible n d A m D B`: (i) `M ≥ 1`, (ii) `equations < unknowns`, (iii) `d + 1 < B < A` and
  `B² > n (d + 1)`, with `1 ≤ d` and `A ≤ n`; decidable, so a concrete instance is checked by
  `decide`;
* `nAff q n d A m D B = D² + jl n B (d + 1) max(q, C(n, 2)) + 4 d² M² D³ (n / (A - B))²`, the
  numerator of `ε_aff = nAff / q²` at one admissible triple. `nAffPersistent` is its middle term
  and `nAffRest` the other two.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset

@[expose] public section

/-- `M = min(D, ⌊(m A - D - 1) / d⌋)`. -/
def bigM (d A m D : ℕ) : ℕ := min D ((m * A - D - 1) / d)

/-- The unknowns of the interpolation, `Σ_{j ≤ M} (m A - D - d j)(D - j + 1)`. -/
def unknowns (d A m D : ℕ) : ℕ :=
  ∑ j ∈ range (bigM d A m D + 1), (m * A - D - d * j) * (D - j + 1)

/-- The equations of the interpolation, `n Σ_{s ≤ min(m - 1, M)} (m - s)(D - s + 1)`. -/
def equations (n d A m D : ℕ) : ℕ :=
  n * ∑ s ∈ range (min (m - 1) (bigM d A m D) + 1), (m - s) * (D - s + 1)

/-- **Admissible interpolation parameters** (Annex B, `def:epsaff`), with the standing
hypotheses `1 ≤ d` and `A ≤ n` (the Rust's `hypotheses`). -/
def Admissible (n d A m D B : ℕ) : Prop :=
  1 ≤ d ∧ A ≤ n ∧ 1 ≤ m ∧ 1 ≤ bigM d A m D ∧ equations n d A m D < unknowns d A m D ∧
    d + 1 < B ∧ B < A ∧ n * (d + 1) < B * B

instance (n d A m D B : ℕ) : Decidable (Admissible n d A m D B) := by
  unfold Admissible; infer_instance

/-- The persistent term of the affine MCA count, `jl n B (d + 1) max(q, C(n, 2))`. -/
def nAffPersistent (q n d B : ℕ) : ℕ := jl n B (d + 1) * max q (n.choose 2)

/-- The other two terms, `D² + 4 d² M² D³ (n / (A - B))²`. -/
def nAffRest (n d A m D B : ℕ) : ℚ :=
  (D : ℚ) ^ 2 + 4 * (d : ℚ) ^ 2 * (bigM d A m D : ℚ) ^ 2 * (D : ℚ) ^ 3 *
    ((n : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2

/-- **The affine MCA count** at one admissible triple:
`D² + jl n B (d + 1) max(q, C(n, 2)) + 4 d² M² D³ (n / (A - B))²`; `ε_aff` is the least of these
over admissible triples, divided by `q²`. -/
def nAff (q n d A m D B : ℕ) : ℚ := nAffPersistent q n d B + nAffRest n d A m D B

/-- The worked example of [CYWZ26, Section 5.1] and of the Rust's `worked_example` test:
`n = 2^20`, `d = 2^18`, `A = 576717`, `m = 3`, `D = 49`, `B = 567980`. -/
example : bigM (2 ^ 18) 576717 3 49 = 6 ∧ jl (2 ^ 20) 567980 (2 ^ 18 + 1) = 6 ∧
    jl (2 ^ 20) (576717 - 1) (2 ^ 18) = 5 := by
  decide +kernel

example : Admissible (2 ^ 20) (2 ^ 18) 576717 3 49 567980 := by
  decide +kernel

end
end LeanVM.Protocol.Whir.AffineCombiner
