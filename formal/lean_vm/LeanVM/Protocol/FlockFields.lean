/-
  LeanVM.Protocol.FlockFields

  Facts about leanVM's fields `K = GF(2^64)` and `E = K[y]/(y^3+y+1)` that the Flock phase's
  knowledge soundness uses: the Frobenius periods, ring-switching injectivity, and the
  `F_2`-independence of the fixed coordinates' weights.
-/

module

public import LeanVM.Spec.Verifier
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Protocol.Blake2sHash
public import LeanVM.Parameters.Field
public import LeanVM.Parameters.Generator
public import LeanVM.Protocol.Field
public import LeanVM.Protocol.ToCompPoly.Multilinear
import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.LinearCombination

/-!
# Field facts for the Flock phase

Two statements about the fields `K = GF(2^64)` and `E = K[y]/(y^3 + y + 1)`
(`LeanVM.Parameters.Field`) on which the Flock phase's knowledge soundness rests, transcribed
from the specification at leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`. The concrete
field facts underneath are kernel checks (`decide +kernel` on `K` words); the rest is algebra.

* **Ring-switching injectivity**, `ringSwitch_injective` (Annex A, §A.3, "Sixty-four terms",
  `doc/leanvm/body/a-ring-switching.tex`). A family `δ : Fin 64 → E` with
  `Σ_i x^i · δ_i^(2^k) = 0` for every `k < 64` is zero. The specification's two steps are
  `limbs_eq_zero_of_frob` (`1, y^(2^k), y^(2^(k+1))` is a `K`-basis of `E`, so each limb family
  satisfies the same equations in `K`) and `eq_zero_of_frob_sums_K` (the polynomial
  `Σ_i d_i X^i`, of degree below 64, vanishes at the 64 conjugates `x^(2^m)` of `x = g`, which
  are distinct by `g_conj_injective`).
* **The fixed coordinates' weights are `F_2`-independent**, `fixedWeights_independent`: the
  hypothesis of the partially fixed zerocheck (`lem:fixed-zerocheck`, §3,
  `doc/leanvm/body/03-proving-primitives.tex`), which Annex C, §C.2
  (`doc/leanvm/body/c-flock-protocol.tex`) asserts for the seven fixed coordinates
  `φ_8(0xF7), φ_8(0x53), φ_8(0xB5)` and `m_j = G_j / (1 + G_j)`, `G_j = g0^(2^j)`, `j < 4`.
  The weight at index `a + 8h` factors as `β_a · γ_h`: the `φ_8` coordinates give eight
  `β_a ∈ GF(2^8)`, and `γ_h = g0^h / Π_j (1 + G_j)`. A vanishing `0/1` combination with
  coefficients `c_{a,h}` makes the polynomial `Σ_h ε_h X^h`, `ε_h = Σ_a c_{a,h} β_a ∈ GF(2^8)`,
  vanish at `g0`, hence at its 16 distinct conjugates `g0^(2^(8m))`, `m < 16`, over `GF(2^8)`;
  so every `ε_h` is zero, and since the `β_a` are `F_2`-independent every `c_{a,h}` is zero.
* The Frobenius periods `a^(2^64) = a` on `K` and `a^(2^192) = a` on `E`.

The kernel checks: `x^(2^d) ≠ x` for `0 < d < 64`; `β_a^(2^8) = β_a` and the
`F_2`-independence of the eight `β_a` in `K`; and `g0^(2^(8d)) ≠ g0` for `0 < d < 16`, computed
on limb triples, since squaring is `(a, b, c) ↦ (a², c², b² + c²)` on the limbs of
`a + b·y + c·y²` and `E`'s own operations do not reduce in the kernel.

## Wrong readings excluded

* `fixedWeights_independent` is independence over `F_2`, with `0/1` coefficients. Over `K` the
  128 weights are dependent: they lie in `E`, of dimension 3 over `K`.
* `ringSwitch_injective` needs all 64 twists `k < 64`: `δ ↦ (Σ_i x^i · δ_i^(2^k))_k` is
  `F_2`-linear from `E^64`, so fewer than 64 twists cannot make it injective.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

/-! ## `ofK` as a ring hom -/

private theorem ofK_zero : ofK 0 = 0 := map_zero (algebraMap K E)

private theorem ofK_one : ofK 1 = 1 := map_one (algebraMap K E)

private theorem ofK_sub (a b : K) : ofK (a - b) = ofK a - ofK b := map_sub (algebraMap K E) a b

private theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

private theorem ofK_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    ofK (∑ i ∈ s, f i) = ∑ i ∈ s, ofK (f i) :=
  map_sum (algebraMap K E) f s

private theorem ofK_prod {ι : Type*} (s : Finset ι) (f : ι → K) :
    ofK (∏ i ∈ s, f i) = ∏ i ∈ s, ofK (f i) :=
  map_prod (algebraMap K E) f s

/-! ## Frobenius periods -/

/-- Every `a : K` satisfies `a ^ 2 ^ 64 = a`. -/
theorem K.pow_two_pow_sixtyFour (a : K) : a ^ 2 ^ 64 = a := by
  have h := FiniteField.pow_card a
  -- `simp only`, not `rw`: a goal mentioning `Fintype.card K` makes the elaborator enumerate `K`.
  simp only [BF64.card_bf64] at h
  exact h

/-- Every `a : E` satisfies `a ^ 2 ^ 192 = a`. -/
theorem E.pow_two_pow_oneNinetyTwo (a : E) : a ^ 2 ^ 192 = a := by
  have h := FiniteField.pow_card a
  simp only [card_E] at h
  exact h

/-- In characteristic two, `x^(2^a) = x^(2^b)` with `a ≤ b` gives `x^(2^(b-a)) = x`. -/
private theorem frob_cancel {R : Type*} [CommRing R] [IsReduced R] [ExpChar R 2] (x : R)
    {a b : ℕ} (hab : a ≤ b) (h : x ^ 2 ^ a = x ^ 2 ^ b) : x ^ 2 ^ (b - a) = x := by
  apply iterateFrobenius_inj R 2 a
  simp only [iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hab]
  exact h.symm

/-- The Frobenius `x ↦ x^(2^m)` of a weighted sum of powers. -/
private theorem frob_sum {R : Type*} [CommRing R] [ExpChar R 2] {n : ℕ} (x : R) (v : Fin n → R)
    (m : ℕ) :
    (∑ i : Fin n, x ^ i.val * v i) ^ 2 ^ m = ∑ i : Fin n, (x ^ 2 ^ m) ^ i.val * v i ^ 2 ^ m := by
  rw [sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow, pow_right_comm x i.val (2 ^ m)]

/-! ## The conjugates of `x` -/

/-- Kernel check: `x^(2^d) ≠ x` for `0 < d < 64`. -/
private theorem g_frob_ne : ∀ d : Fin 64, d.val ≠ 0 → g ^ 2 ^ d.val ≠ g := by
  decide +kernel

/-- The 64 conjugates `x^(2^m)`, `m < 64`, of `x = g` are distinct. -/
theorem g_conj_injective : Function.Injective fun m : Fin 64 ↦ g ^ 2 ^ m.val := by
  intro a b hab
  simp only at hab
  by_contra hne
  rcases lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h)) with hlt | hlt
  · exact g_frob_ne ⟨b.val - a.val, by omega⟩ (Nat.sub_ne_zero_of_lt hlt)
      (frob_cancel g hlt.le hab)
  · exact g_frob_ne ⟨a.val - b.val, by omega⟩ (Nat.sub_ne_zero_of_lt hlt)
      (frob_cancel g hlt.le hab.symm)

/-- A family of `K` whose sums `Σ_i x^i · d_i^(2^k)` vanish for every `k < 64` is zero. -/
theorem eq_zero_of_frob_sums_K (d : Fin 64 → K)
    (h : ∀ k < 64, ∑ i : Fin 64, g ^ i.val * d i ^ 2 ^ k = 0) : ∀ i, d i = 0 := by
  have hroot : ∀ m : Fin 64, ∑ i : Fin 64, (g ^ 2 ^ m.val) ^ i.val * d i = 0 := by
    intro m
    by_cases hm : m.val = 0
    · simpa [hm] using h 0 (by norm_num)
    · have hk : (∑ i : Fin 64, g ^ i.val * d i ^ 2 ^ (64 - m.val)) ^ 2 ^ m.val = 0 := by
        rw [h _ (by omega), zero_pow (pow_ne_zero _ two_ne_zero)]
      rw [frob_sum] at hk
      rw [← hk]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← pow_mul (d i), ← pow_add, Nat.sub_add_cancel (by omega), K.pow_two_pow_sixtyFour]
  exact congrFun (Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero g_conj_injective hroot)

/-! ## Ring switching -/

/-- `1, y^(2^k), y^(2^(k+1))` are `K`-independent in `E`. -/
theorem limbs_eq_zero_of_frob (k : ℕ) (hk : k < 192) (a b c : K)
    (h : ofK a + ofK b * y ^ 2 ^ k + ofK c * (y ^ 2 ^ k) ^ 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hy : (y ^ 2 ^ k) ^ 2 ^ (192 - k) = y := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk.le, E.pow_two_pow_oneNinetyTwo]
  have h' : (ofK a + ofK b * y ^ 2 ^ k + ofK c * (y ^ 2 ^ k) ^ 2) ^ 2 ^ (192 - k) = 0 := by
    rw [h, zero_pow (pow_ne_zero _ two_ne_zero)]
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow,
    pow_right_comm (y ^ 2 ^ k) 2 (2 ^ (192 - k)), hy, ← ofK_pow, ← ofK_pow, ← ofK_pow,
    ← ofLimbs_eq] at h'
  have h0 := congrArg (fun z : E ↦ z.limb 0) h'
  have h1 := congrArg (fun z : E ↦ z.limb 1) h'
  have h2 := congrArg (fun z : E ↦ z.limb 2) h'
  simp only [limb_ofLimbs, limb_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hn : 2 ^ (192 - k) ≠ 0 := pow_ne_zero _ two_ne_zero
  exact ⟨(pow_eq_zero_iff hn).mp h0, (pow_eq_zero_iff hn).mp h1, (pow_eq_zero_iff hn).mp h2⟩

/-- The Frobenius `x ↦ x^(2^k)` on limbs. -/
private theorem frob_limbs (x : E) (k : ℕ) :
    x ^ 2 ^ k = ofK (x.limb 0 ^ 2 ^ k) + ofK (x.limb 1 ^ 2 ^ k) * y ^ 2 ^ k +
      ofK (x.limb 2 ^ 2 ^ k) * (y ^ 2 ^ k) ^ 2 := by
  conv_lhs => rw [E.eq_sum_limbs x]
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, pow_right_comm y 2 (2 ^ k),
    ofK_pow, ofK_pow, ofK_pow]

/-- **Ring-switching injectivity** (Annex A, §A.3): a family of `E` whose sums
`Σ_i x^i · δ_i^(2^k)` vanish for every `k < 64` is zero. -/
theorem ringSwitch_injective (δ : Fin 64 → E)
    (h : ∀ k < 64, ∑ i : Fin 64, algebraMap K E (g ^ i.val) * δ i ^ 2 ^ k = 0) :
    ∀ i, δ i = 0 := by
  have hsplit : ∀ k < 64, (∑ i : Fin 64, g ^ i.val * (δ i).limb 0 ^ 2 ^ k) = 0 ∧
      (∑ i : Fin 64, g ^ i.val * (δ i).limb 1 ^ 2 ^ k) = 0 ∧
      (∑ i : Fin 64, g ^ i.val * (δ i).limb 2 ^ 2 ^ k) = 0 := by
    intro k hk
    apply limbs_eq_zero_of_frob k (by omega)
    have e : ∀ i : Fin 64, algebraMap K E (g ^ i.val) * δ i ^ 2 ^ k =
        ofK (g ^ i.val * (δ i).limb 0 ^ 2 ^ k) +
          ofK (g ^ i.val * (δ i).limb 1 ^ 2 ^ k) * y ^ 2 ^ k +
          ofK (g ^ i.val * (δ i).limb 2 ^ 2 ^ k) * (y ^ 2 ^ k) ^ 2 := by
      intro i
      rw [frob_limbs (δ i) k, ofK_mul, ofK_mul, ofK_mul]
      change ofK (g ^ i.val) * _ = _
      ring
    rw [← h k hk, Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ofK_sum, ofK_sum, ofK_sum]
  have ha := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 0) fun k hk ↦ (hsplit k hk).1
  have hb := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 1) fun k hk ↦ (hsplit k hk).2.1
  have hc := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 2) fun k hk ↦ (hsplit k hk).2.2
  intro i
  refine E.ext fun j ↦ ?_
  rw [limb_zero]
  fin_cases j
  exacts [ha i, hb i, hc i]

/-! ## The fixed coordinates -/

/-! ### The `φ_8` coordinates -/

/-- `φ_8` of the three fixed bytes. -/
private def phiK (j : Fin 3) : K := Flock.phi8 Flock.fixedBytes[j]

/-- The Lagrange weight of the three `φ_8` coordinates at the low index `a`, in `K`. -/
private def betaK (a : Fin (2 ^ 3)) : K :=
  ∏ j : Fin 3, if a.val.testBit j then phiK j else 1 - phiK j

/-- Kernel check: each `betaK a` lies in `GF(2^8)`, `betaK a ^ 2 ^ 8 = betaK a`. -/
private theorem betaK_frob : ∀ a : Fin (2 ^ 3), betaK a ^ 2 ^ 8 = betaK a := by
  decide +kernel

/-- Kernel check: the eight `betaK a` are `F_2`-independent. -/
private theorem betaK_independent : ∀ f : Fin (2 ^ 3) → Bool,
    ∑ a, (if f a then betaK a else 0) = 0 → ∀ a, f a = false := by
  decide +kernel

/-- The low Lagrange basis of the fixed point is `betaK`. -/
private theorem lagrangeBasis_low (a : Fin (2 ^ 3)) :
    (lagrangeBasis (lowVec (k := 3) (m := 4) Flock.fixedPoint))[a] = ofK (betaK a) := by
  rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ a.isLt, betaK, ofK_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  have hj : (lowVec (k := 3) (m := 4) Flock.fixedPoint)[j] = ofK (phiK j) := by
    simp only [lowVec, Fin.getElem_fin, Vector.getElem_ofFn]
    fin_cases j <;> rfl
  rw [hj]
  split_ifs
  · rfl
  · rw [ofK_sub, ofK_one]

/-! ### The `g0` coordinates -/

/-- `x^h` as the product of `x^(2^j)` over the set bits `j` of `h`. -/
private theorem prod_testBit_pow {M : Type*} [CommMonoid M] (x : M) (n h : ℕ) (hh : h < 2 ^ n) :
    ∏ j : Fin n, (if h.testBit j then x ^ 2 ^ j.val else 1) = x ^ h := by
  induction n generalizing x h with
  | zero =>
    have h0 : h = 0 := by simpa using hh
    simp [h0]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have hh' : h / 2 < 2 ^ n := by rw [pow_succ] at hh; omega
    have e : ∀ j : Fin n, (if h.testBit (j.succ : ℕ) then x ^ 2 ^ (j.succ : ℕ) else 1) =
        if (h / 2).testBit j then (x ^ 2) ^ 2 ^ j.val else 1 := by
      intro j
      rw [Fin.val_succ, Nat.testBit_add_one, ← pow_mul, pow_succ']
    have e0 : (if h.testBit ((0 : Fin (n + 1)) : ℕ) then x ^ 2 ^ ((0 : Fin (n + 1)) : ℕ) else 1) =
        x ^ (h % 2) := by
      rcases Nat.mod_two_eq_zero_or_one h with h0 | h1 <;> simp [Nat.testBit_zero, *]
    rw [Finset.prod_congr rfl fun j _ ↦ e j, ih (x ^ 2) (h / 2) hh', ← pow_mul, e0, ← pow_add,
      Nat.mod_add_div]

/-- `1 + g0` is nonzero: its `y` limb is. -/
private theorem one_add_g0_ne_zero : 1 + Flock.g0 ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : E ↦ z.limb 1) h
  rw [← ofK_one, ofK_eq_ofLimbs, Flock.g0, add_limbs] at h1
  simp only [limb_ofLimbs, limb_zero] at h1
  revert h1
  decide +kernel

/-- `1 + g0^(2^j)` is nonzero. -/
private theorem one_add_g0_pow_ne_zero (j : ℕ) : 1 + Flock.g0 ^ 2 ^ j ≠ 0 := by
  have e : 1 + Flock.g0 ^ 2 ^ j = (1 + Flock.g0) ^ 2 ^ j := by rw [add_pow_char_pow, one_pow]
  rw [e]
  exact pow_ne_zero _ one_add_g0_ne_zero

/-- A medium coordinate's Lagrange factor times `1 + G`. -/
private theorem medium_factor (G : E) (hG : 1 + G ≠ 0) (bit : Bool) :
    (if bit then G / (1 + G) else 1 - G / (1 + G)) * (1 + G) = if bit then G else 1 := by
  cases bit
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sub_mul, one_mul, div_mul_cancel₀ G hG, add_sub_cancel_right]
  · simp only [↓reduceIte]
    exact div_mul_cancel₀ G hG

/-- The high Lagrange basis of the fixed point, times `∏_j (1 + g0^(2^j))`, is `g0^h`. -/
private theorem lagrangeBasis_high (h : Fin (2 ^ 4)) :
    (lagrangeBasis (highVec (k := 3) (m := 4) Flock.fixedPoint))[h] *
      ∏ j : Fin 4, (1 + Flock.g0 ^ 2 ^ j.val) = Flock.g0 ^ h.val := by
  rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ h.isLt, ← Finset.prod_mul_distrib,
    ← prod_testBit_pow Flock.g0 4 h.val h.isLt]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  have hj : (highVec (k := 3) (m := 4) Flock.fixedPoint)[j] = Flock.mediumCoord j.val := by
    simp only [highVec, Fin.getElem_fin, Vector.getElem_ofFn]
    fin_cases j <;> rfl
  rw [hj, Flock.mediumCoord]
  exact medium_factor _ (one_add_g0_pow_ne_zero j.val) _

/-! ### The conjugates of `g0` -/

/-- Squaring on limbs: `(a + b·y + c·y²)² = a² + c²·y + (b² + c²)·y²`, since `y⁴ = y² + y`. -/
private theorem sq_ofLimbs (a b c : K) :
    E.ofLimbs a b c ^ 2 = E.ofLimbs (a ^ 2) (c ^ 2) (b ^ 2 + c ^ 2) := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hy4 : y ^ 4 = y ^ 2 + y := by
    rw [show y ^ 4 = y * y ^ 3 by ring, y_pow_three]
    ring
  rw [ofLimbs_eq, ofLimbs_eq, ofK_add, ofK_pow, ofK_pow, ofK_pow]
  linear_combination (ofK c) ^ 2 * hy4 + (ofK a * ofK b * y + ofK a * ofK c * y ^ 2 +
    ofK b * ofK c * y ^ 3) * h2

/-- A word of `E` from its limb triple. -/
private def toE (t : K × K × K) : E := E.ofLimbs t.1 t.2.1 t.2.2

/-- Squaring on limb triples (`sq_ofLimbs`). -/
private def sqTriple (t : K × K × K) : K × K × K := (t.1 ^ 2, t.2.2 ^ 2, t.2.1 ^ 2 + t.2.2 ^ 2)

/-- Eight squarings on limb triples. -/
private def frob8Triple (t : K × K × K) : K × K × K :=
  sqTriple (sqTriple (sqTriple (sqTriple (sqTriple (sqTriple (sqTriple (sqTriple t)))))))

/-- The limbs of `g0`. -/
private def g0Triple : K × K × K := (Flock.g0.limb 0, Flock.g0.limb 1, Flock.g0.limb 2)

/-- `m` applications of `f`. -/
private def iter {α : Type} (f : α → α) : ℕ → α → α
  | 0, t => t
  | m + 1, t => iter f m (f t)

/-- No application. -/
private theorem iter_zero {α : Type} (f : α → α) (t : α) : iter f 0 t = t := rfl

/-- One more application, taken first. -/
private theorem iter_succ {α : Type} (f : α → α) (m : ℕ) (t : α) :
    iter f (m + 1) t = iter f m (f t) := rfl

/-- The `m` values `t, f t, …, f^(m-1) t`. -/
private def orbit {α : Type} (f : α → α) : ℕ → α → List α
  | 0, _ => []
  | m + 1, t => t :: orbit f m (f t)

/-- Kernel check: `d` rounds of eight squarings move the limbs of `g0`, for `1 ≤ d ≤ 15`. -/
private theorem g0_orbit_ne :
    (orbit frob8Triple 15 (frob8Triple g0Triple)).all (· ≠ g0Triple) = true := by
  decide +kernel

/-- A word determines its limb triple. -/
private theorem toE_injective : Function.Injective toE := by
  intro s t hst
  have h0 := congrArg (fun z : E ↦ z.limb 0) hst
  have h1 := congrArg (fun z : E ↦ z.limb 1) hst
  have h2 := congrArg (fun z : E ↦ z.limb 2) hst
  simp only [toE, limb_ofLimbs] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- `g0` is the word of its limb triple. -/
private theorem toE_g0Triple : toE g0Triple = Flock.g0 := ofLimbs_limb Flock.g0

/-- `x ↦ x^(2^8)` on limb triples is eight squarings. -/
private theorem frob8_toE (t : K × K × K) : toE t ^ 2 ^ 8 = toE (frob8Triple t) := by
  have e : ∀ x : E, x ^ 2 ^ 8 = (((((((x ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := fun x ↦ by
    ring
  have hsq : ∀ s : K × K × K, toE s ^ 2 = toE (sqTriple s) := fun s ↦ sq_ofLimbs _ _ _
  rw [e]
  simp only [hsq]
  rfl

/-- `x ↦ x^(2^(8m))` on limb triples is `m` rounds of eight squarings. -/
private theorem toE_pow_iter (m : ℕ) (t : K × K × K) :
    toE t ^ 2 ^ (8 * m) = toE (iter frob8Triple m t) := by
  induction m generalizing t with
  | zero => rw [Nat.mul_zero, pow_zero, pow_one, iter_zero]
  | succ m ih => rw [show 8 * (m + 1) = 8 + 8 * m by ring, pow_add, pow_mul, frob8_toE, ih,
    iter_succ]

/-- `f^i t` lies in the orbit of `t` of length `n` for `i < n`. -/
private theorem mem_orbit {α : Type} (f : α → α) (n : ℕ) :
    ∀ (t : α) (i : ℕ), i < n → iter f i t ∈ orbit f n t := by
  induction n with
  | zero => intro t i hi; omega
  | succ n ih =>
    intro t i hi
    cases i with
    | zero => simp only [orbit, iter_zero, List.mem_cons_self]
    | succ i =>
      simp only [orbit, iter_succ]
      exact List.mem_cons_of_mem _ (ih _ i (by omega))

/-- `g0^(2^(8d)) ≠ g0` for `0 < d < 16`. -/
private theorem g0_frob_ne (d : ℕ) (hd0 : d ≠ 0) (hd : d < 16) :
    Flock.g0 ^ 2 ^ (8 * d) ≠ Flock.g0 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hall := List.all_eq_true.mp g0_orbit_ne _
    (mem_orbit frob8Triple 15 (frob8Triple g0Triple) e (by omega))
  intro heq
  rw [← toE_g0Triple, toE_pow_iter, iter_succ] at heq
  exact of_decide_eq_true hall (toE_injective heq)

/-- The 16 conjugates `g0^(2^(8m))`, `m < 16`, are distinct. -/
private theorem g0_conj_injective :
    Function.Injective fun m : Fin (2 ^ 4) ↦ Flock.g0 ^ 2 ^ (8 * m.val) := by
  intro a b hab
  simp only at hab
  by_contra hne
  rcases lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h)) with hlt | hlt
  · apply g0_frob_ne (b.val - a.val) (by omega) (by omega)
    have := frob_cancel Flock.g0 (by omega : 8 * a.val ≤ 8 * b.val) hab
    rwa [show 8 * b.val - 8 * a.val = 8 * (b.val - a.val) by omega] at this
  · apply g0_frob_ne (a.val - b.val) (by omega) (by omega)
    have := frob_cancel Flock.g0 (by omega : 8 * b.val ≤ 8 * a.val) hab.symm
    rwa [show 8 * a.val - 8 * b.val = 8 * (a.val - b.val) by omega] at this

/-! ### Independence -/

/-- A fixed point of `x ↦ x^(2^8)` is fixed by `x ↦ x^(2^(8m))`. -/
private theorem frob8_period (x : K) (hx : x ^ 2 ^ 8 = x) (m : ℕ) : x ^ 2 ^ (8 * m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [show 8 * (m + 1) = 8 * m + 8 by ring, pow_add, pow_mul, ih, hx]

/-- **The fixed coordinates' weights are `F_2`-independent** (the hypothesis of the
specification's partially fixed zerocheck, `lem:fixed-zerocheck` in §3, which the pinned Rust
only tests numerically, `tests::friendly_challenges_f2_independent` in
`crates/flock/src/zerocheck/univariate_skip_optimized.rs`): a `0/1` combination of the 128
weights `eq(fixedPoint, v)` that vanishes is zero. -/
theorem fixedWeights_independent (c : Fin (2 ^ 7) → E) (hc : ∀ v, c v = 0 ∨ c v = 1)
    (h : ∑ v : Fin (2 ^ 7), (lagrangeBasis Flock.fixedPoint)[v] * c v = 0) : ∀ v, c v = 0 := by
  obtain ⟨bits, hbits⟩ : ∃ bits : Fin (2 ^ 7) → Bool, ∀ v, c v = if bits v then 1 else 0 := by
    refine ⟨fun v ↦ decide (c v = 1), fun v ↦ ?_⟩
    rcases hc v with h0 | h1
    · simp [h0]
    · simp [h1]
  -- `e j`: the `F_2`-combination of the `betaK a` that the slice at high index `j` selects.
  set e : Fin (2 ^ 4) → K := fun j ↦ ∑ a : Fin (2 ^ 3),
    if bits (cubeIndex a j) then betaK a else 0 with he
  have hε : ∀ j : Fin (2 ^ 4),
      ∑ a : Fin (2 ^ 3), ofK (betaK a) * c (cubeIndex a j) = ofK (e j) := by
    intro j
    simp only [he, ofK_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hbits]
    split_ifs
    · rw [mul_one]
    · rw [mul_zero, ofK_zero]
  have h1 : ∑ j : Fin (2 ^ 4),
      (lagrangeBasis (highVec (k := 3) (m := 4) Flock.fixedPoint))[j] * ofK (e j) = 0 := by
    rw [← h, sum_cube_split (k := 3) (m := 4)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hε j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [lagrangeBasis_cubeIndex (k := 3) (m := 4), lagrangeBasis_low]
    ring
  have h2 : ∑ j : Fin (2 ^ 4), Flock.g0 ^ j.val * ofK (e j) = 0 := by
    have := congrArg (· * ∏ j : Fin 4, (1 + Flock.g0 ^ 2 ^ j.val)) h1
    simp only [zero_mul, Finset.sum_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← lagrangeBasis_high j]
    ring
  have he8 : ∀ j, e j ^ 2 ^ 8 = e j := by
    intro j
    simp only [he]
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    split_ifs
    · exact betaK_frob a
    · exact zero_pow (pow_ne_zero _ two_ne_zero)
  have hroot : ∀ m : Fin (2 ^ 4),
      ∑ j : Fin (2 ^ 4), (Flock.g0 ^ 2 ^ (8 * m.val)) ^ j.val * ofK (e j) = 0 := by
    intro m
    have hk : (∑ j : Fin (2 ^ 4), Flock.g0 ^ j.val * ofK (e j)) ^ 2 ^ (8 * m.val) = 0 := by
      rw [h2, zero_pow (pow_ne_zero _ two_ne_zero)]
    rw [frob_sum] at hk
    rw [← hk]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← ofK_pow, frob8_period _ (he8 j)]
  have hzero := Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero g0_conj_injective hroot
  have hbits0 : ∀ (a : Fin (2 ^ 3)) (j : Fin (2 ^ 4)), bits (cubeIndex a j) = false := by
    intro a j
    have hej : e j = 0 := ofK_injective (by rw [ofK_zero]; exact congrFun hzero j)
    exact betaK_independent (fun a ↦ bits (cubeIndex a j)) hej a
  intro v
  obtain ⟨⟨a, j⟩, rfl⟩ := (cubeSplit 3 4).surjective v
  simp only [cubeSplit_apply, hbits, hbits0, Bool.false_eq_true, ↓reduceIte]

end
end LeanVM.Protocol
