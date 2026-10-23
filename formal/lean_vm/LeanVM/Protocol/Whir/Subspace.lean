/-
  LeanVM.Protocol.Whir.Subspace

  The F₂-subspaces `U_i` of `K` spanned by the first `i` powers of `x`, their vanishing
  polynomials `W_i`, and the normalized `Ŵ_i = W_i / W_i(e_i)`: the subspace polynomials of
  leanVM's binary Reed-Solomon code.
-/

module

public import LeanVM.Parameters.Field
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Subspace vanishing polynomials

Annex D ("Novel polynomial basis and additive NTT", `app:ntt`; Annex B §B.6 until `127510d1`) of
the leanVM specification, `doc/leanvm/body/d-novel-basis.tex:2-27` at leanVM pin
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`. The definitions are the Annex's, and the
lemma is its Lemma `lem:subspace`, parts (i) and (ii) proved here; its first sentence, added at
`127510d1` (each `W_i` has only the monomials `X^(2^j)`), is not formalized.

* `basisVec c` is `e_c = x^c`, the word `K.ofBits (2^c)`; `e_0 = 1`.
* `subspace i` is `U_i = ⟨e_0, …, e_{i-1}⟩_{F₂}`, the words `K.ofBits v` for `v < 2^i`
  (`ofBits_eq_sum`: the word with bits `v` is `Σ_c v_c e_c`). Below `2^64` the words are distinct
  (`ofBits_injOn`), so `|U_i| = 2^i` for `i ≤ 64`.
* `vanishing i` is `W_i(X) = ∏_{u ∈ U_i} (X + u)`, written as the product over `v < 2^i`
  (`vanishing_eq_prod_subspace` for `i ≤ 64`); `vanishingAt i a` is its computable evaluation.
  Monic of degree `2^i` (`vanishing_monic`, `natDegree_vanishing`), with roots exactly `U_i`
  (`vanishingAt_eq_zero_iff`).
* Lemma `lem:subspace`: (i) `W_{i+1} = W_i·(W_i + W_i(e_i))` (`vanishing_succ`) with
  `W_i(e_i) ≠ 0` for `i < 64` (`vanishingAt_basisVec_ne_zero`); (ii) `W_i(X + Y) = W_i(X) + W_i(Y)`
  in `K[X, Y]` (`vanishing_add_bivariate`, from `aeval_vanishing_add` in any commutative
  `K`-algebra), `W_i(X + a) = W_i(X) + W_i(a)` in `K[X]` (`vanishing_comp_add`), so `W_i` is
  additive on `K` (`vanishingAt_add`).
* `normVanishing i` is `Ŵ_i = W_i / W_i(e_i)`, with `Ŵ_i(e_i) = 1` (`normVanishingAt_basisVec`),
  degree `2^i` for `i < 64` (`natDegree_normVanishing`), additive, and `Ŵ_0 = X`
  (`normVanishing_zero`).

## Wrong readings excluded

* `W_i` vanishes on the *subspace* `U_i`, not on the first `2^i` integers read as field elements
  under some other encoding: `K.ofBits v` is the word whose bit `c` is the coefficient of `x^c`.
* The recurrence (i) and the identity (ii) hold for every `i`; only `W_i(e_i) ≠ 0` needs
  `i < 64`. At `i ≥ 64` the word `2^i` wraps to `0`, `e_i = 0`, and `Ŵ_i` is `0` by Lean's
  convention `0⁻¹ = 0`.
-/

namespace LeanVM.Protocol.Whir

open LeanVM.Parameters Polynomial

@[expose] public section

/-! ## Words and the basis `e_c` -/

/-- `e_c = x^c`, the word with the single bit `c`. -/
def basisVec (c : ℕ) : K := K.ofBits (2 ^ c)

/-- `U_i = ⟨e_0, …, e_{i-1}⟩_{F₂}`, as the words whose bits lie below `i`. -/
def subspace (i : ℕ) : Finset K := (Finset.range (2 ^ i)).image K.ofBits

/-- `e_0 = 1`. -/
theorem basisVec_zero : basisVec 0 = 1 := rfl

/-- `K.ofBits 0 = 0`. -/
@[simp] theorem ofBits_zero : K.ofBits 0 = 0 := rfl

/-- A word below `2^64` is read back exactly. -/
theorem toNat_ofBits {n : ℕ} (hn : n < 2 ^ 64) : (K.ofBits n).toBitVec.toNat = n := by
  simpa [K.ofBits] using hn

/-- Words below `2^64` are distinct field elements. -/
theorem ofBits_injOn : Set.InjOn K.ofBits {n | n < 2 ^ 64} := by
  intro a ha b hb h
  rw [← toNat_ofBits ha, ← toNat_ofBits hb, h]

/-- A word below `2^64` is zero only when it is `0`. -/
theorem ofBits_eq_zero_iff {n : ℕ} (hn : n < 2 ^ 64) : K.ofBits n = 0 ↔ n = 0 :=
  ⟨fun h ↦ ofBits_injOn (show n < 2 ^ 64 from hn) (show 0 < 2 ^ 64 by norm_num) h,
    fun h ↦ h ▸ ofBits_zero⟩

/-- Below `2^i`, adding `2^i` sets a bit that is clear: it is the exclusive or. -/
theorem two_pow_add_eq_xor {i v : ℕ} (hv : v < 2 ^ i) : 2 ^ i + v = 2 ^ i ^^^ v := by
  have h := Nat.two_pow_add_eq_or_of_lt hv 1
  rw [mul_one] at h
  rw [h]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hj : i = j
  · subst hj
    simp [Nat.testBit_lt_two_pow hv]
  · simp [hj]

/-- Sum in `K` is bitwise exclusive or of words. -/
theorem ofBits_xor (a b : ℕ) : K.ofBits (a ^^^ b) = K.ofBits a + K.ofBits b := by
  simp only [K.ofBits, BitVec.ofNat_xor]
  rfl

/-- `x_{2^i + v} = e_i + x_v` for `v < 2^i`: the coset `e_i + U_i`. -/
theorem ofBits_two_pow_add {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits (2 ^ i + v) = basisVec i + K.ofBits v := by
  rw [two_pow_add_eq_xor hv, ofBits_xor, basisVec]

/-- The word with bits `v` is `Σ_c v_c e_c`: `U_i` is the span of `e_0, …, e_{i-1}`. -/
theorem ofBits_eq_sum {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits v = ∑ c ∈ Finset.range i, if v.testBit c then basisVec c else 0 := by
  induction i generalizing v with
  | zero =>
    obtain rfl : v = 0 := by simpa using hv
    simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    by_cases hb : v.testBit i
    · have hlt : v - 2 ^ i < 2 ^ i := by
        have := Nat.ge_two_pow_of_testBit hb
        rw [pow_succ] at hv
        omega
      have hv' : v = 2 ^ i + (v - 2 ^ i) := by
        have := Nat.ge_two_pow_of_testBit hb
        omega
      have hbits : ∀ c < i, v.testBit c = (v - 2 ^ i).testBit c := by
        intro c hc
        conv_lhs => rw [hv']
        exact Nat.testBit_two_pow_add_gt hc _
      have hb' : (2 ^ i + (v - 2 ^ i)).testBit i = true := by rw [← hv']; exact hb
      rw [hv', ofBits_two_pow_add hlt, ih hlt, hb']
      simp only [ite_true]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun c hc ↦ ?_
      rw [← hv', hbits c (Finset.mem_range.mp hc)]
    · have hlt : v < 2 ^ i := by
        by_contra h
        have h1 : 2 ^ i ≤ v := not_lt.mp h
        have : v.testBit i = true := by
          have hv2 : v - 2 ^ i < 2 ^ i := by rw [pow_succ] at hv; omega
          have := Nat.testBit_two_pow_add_eq (v - 2 ^ i) i
          rw [Nat.add_sub_cancel' h1, Nat.testBit_lt_two_pow hv2] at this
          simpa using this
        exact hb this
      simp only [Bool.not_eq_true] at hb
      rw [ih hlt, hb]
      simp

/-! ## The vanishing polynomials -/

/-- `W_i(X) = ∏_{u ∈ U_i} (X + u)`, the product over the words `v < 2^i`. -/
noncomputable def vanishing (i : ℕ) : K[X] := ∏ v ∈ Finset.range (2 ^ i), (X + C (K.ofBits v))

/-- `W_i(a)`, computed from the product. -/
def vanishingAt (i : ℕ) (a : K) : K := ∏ v ∈ Finset.range (2 ^ i), (a + K.ofBits v)

/-- `vanishingAt` evaluates `vanishing`. -/
@[simp] theorem eval_vanishing (i : ℕ) (a : K) : (vanishing i).eval a = vanishingAt i a := by
  simp [vanishing, vanishingAt, eval_prod]

/-- For `i ≤ 64` the product over `v < 2^i` is the product over the subspace `U_i`. -/
theorem vanishing_eq_prod_subspace {i : ℕ} (hi : i ≤ 64) :
    vanishing i = ∏ u ∈ subspace i, (X + C u) := by
  rw [vanishing, subspace, Finset.prod_image]
  intro a ha b hb h
  have hle : 2 ^ i ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hi
  exact ofBits_injOn (show a < 2 ^ 64 from lt_of_lt_of_le (Finset.mem_range.mp ha) hle)
    (show b < 2 ^ 64 from lt_of_lt_of_le (Finset.mem_range.mp hb) hle) h

/-- `W_i` is monic. -/
theorem vanishing_monic (i : ℕ) : (vanishing i).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

/-- `deg W_i = 2^i`. -/
theorem natDegree_vanishing (i : ℕ) : (vanishing i).natDegree = 2 ^ i := by
  rw [vanishing, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _]
  simp

/-- `W_0 = X`. -/
theorem vanishing_zero : vanishing 0 = X := by simp [vanishing]

/-- The roots of `W_i` are exactly `U_i`. -/
theorem vanishingAt_eq_zero_iff (i : ℕ) (a : K) : vanishingAt i a = 0 ↔ a ∈ subspace i := by
  simp only [vanishingAt, Finset.prod_eq_zero_iff, subspace, Finset.mem_image]
  refine exists_congr fun v ↦ and_congr_right fun _ ↦ ?_
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq, eq_comm]

/-- `W_i(X + e_i)` is the product over the coset `e_i + U_i`, the upper half of `U_{i+1}`. -/
private theorem vanishing_succ_split (i : ℕ) :
    vanishing (i + 1) = vanishing i * (vanishing i).comp (X + C (basisVec i)) := by
  rw [vanishing, pow_succ, mul_two, Finset.prod_range_add, vanishing, prod_comp]
  congr 1
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  rw [ofBits_two_pow_add (Finset.mem_range.mp hv)]
  simp only [add_comp, X_comp, C_comp, C_add]
  ring

/-- `(A + B)(A + B + c) = A(A + c) + B(B + c)` in characteristic two. -/
private theorem char_two_cross (A B c : K[X]) :
    (A + B) * (A + B + c) = A * (A + c) + B * (B + c) := by
  linear_combination (A * B) * (CharTwo.two_eq_zero : (2 : K[X]) = 0)

/-- Lemma `lem:subspace`, jointly: (ii) at `i`, then (i) at `i`. -/
private theorem vanishing_comp_add_and_succ (i : ℕ) :
    (∀ a : K, (vanishing i).comp (X + C a) = vanishing i + C (vanishingAt i a)) ∧
      vanishing (i + 1) =
        vanishing i * (vanishing i + C (vanishingAt i (basisVec i))) := by
  have step : ∀ i, (∀ a : K, (vanishing i).comp (X + C a) = vanishing i + C (vanishingAt i a)) →
      vanishing (i + 1) = vanishing i * (vanishing i + C (vanishingAt i (basisVec i))) := by
    intro i h
    rw [vanishing_succ_split, h]
  induction i with
  | zero =>
    refine ⟨fun a ↦ ?_, step 0 fun a ↦ ?_⟩ <;>
    · simp [vanishing_zero, vanishingAt]
  | succ i ih =>
    have hadd : ∀ a : K,
        (vanishing (i + 1)).comp (X + C a) = vanishing (i + 1) + C (vanishingAt (i + 1) a) := by
      intro a
      rw [← eval_vanishing (i + 1) a, ih.2, mul_comp, add_comp, C_comp, ih.1 a, eval_mul,
        eval_add, eval_C, eval_vanishing, C_mul, C_add]
      exact char_two_cross _ _ _
    exact ⟨hadd, step _ hadd⟩

/-- Lemma `lem:subspace` (ii): `W_i(X + a) = W_i(X) + W_i(a)`, a polynomial identity in `X`. -/
theorem vanishing_comp_add (i : ℕ) (a : K) :
    (vanishing i).comp (X + C a) = vanishing i + C (vanishingAt i a) :=
  (vanishing_comp_add_and_succ i).1 a

/-- Lemma `lem:subspace` (i): `W_{i+1} = W_i·(W_i + W_i(e_i))`. -/
theorem vanishing_succ (i : ℕ) :
    vanishing (i + 1) = vanishing i * (vanishing i + C (vanishingAt i (basisVec i))) :=
  (vanishing_comp_add_and_succ i).2

/-- Lemma `lem:subspace` (ii) in any commutative `K`-algebra: `W_i(a + b) = W_i(a) + W_i(b)`. -/
theorem aeval_vanishing_add {A : Type*} [CommRing A] [Algebra K A] (i : ℕ) (a b : A) :
    aeval (a + b) (vanishing i) = aeval a (vanishing i) + aeval b (vanishing i) := by
  have h2 : (2 : A) = 0 := by
    have := congrArg (algebraMap K A) (CharTwo.two_eq_zero : (2 : K) = 0)
    rwa [map_ofNat, map_zero] at this
  induction i with
  | zero => simp [vanishing_zero]
  | succ i ih =>
    simp only [vanishing_succ, map_mul, map_add, aeval_C, ih]
    linear_combination (aeval a (vanishing i) * aeval b (vanishing i)) * h2

/-- Lemma `lem:subspace` (ii) as the bivariate polynomial identity
`W_i(X + Y) = W_i(X) + W_i(Y)` in `K[X, Y]`. -/
theorem vanishing_add_bivariate (i : ℕ) :
    aeval (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) K) (vanishing i) =
      aeval (MvPolynomial.X 0) (vanishing i) + aeval (MvPolynomial.X 1) (vanishing i) :=
  aeval_vanishing_add i _ _

/-- The recurrence (i), evaluated: `W_{i+1}(a) = W_i(a)^2 + W_i(e_i)·W_i(a)`, the update of the
pinned Python's `_subspace_roots` and of the Rust `next_s`. -/
theorem vanishingAt_succ (i : ℕ) (a : K) :
    vanishingAt (i + 1) a = vanishingAt i a ^ 2 + vanishingAt i (basisVec i) * vanishingAt i a := by
  rw [← eval_vanishing, vanishing_succ, eval_mul, eval_add, eval_C, eval_vanishing]
  ring

/-- `W_i` is additive on `K`, hence `F₂`-linear. -/
theorem vanishingAt_add (i : ℕ) (a b : K) :
    vanishingAt i (a + b) = vanishingAt i a + vanishingAt i b := by
  have h := congrArg (eval a) (vanishing_comp_add i b)
  rw [eval_comp, eval_add, eval_X, eval_C, eval_add, eval_C, eval_vanishing,
    eval_vanishing] at h
  exact h

/-- `W_i(0) = 0`. -/
@[simp] theorem vanishingAt_zero (i : ℕ) : vanishingAt i 0 = 0 :=
  (vanishingAt_eq_zero_iff i 0).mpr
    (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.two_pow_pos i), ofBits_zero⟩)

/-- Lemma `lem:subspace`: `W_i(e_i) ≠ 0` for `i < 64`, since `e_i ∉ U_i`. -/
theorem vanishingAt_basisVec_ne_zero {i : ℕ} (hi : i < 64) : vanishingAt i (basisVec i) ≠ 0 := by
  rw [vanishingAt]
  refine Finset.prod_ne_zero_iff.mpr fun v hv ↦ ?_
  have hv' := Finset.mem_range.mp hv
  rw [← ofBits_two_pow_add hv']
  have hlt : 2 ^ i + v < 2 ^ 64 := by
    have : 2 ^ (i + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hi
    rw [pow_succ] at this
    omega
  rw [Ne, ofBits_eq_zero_iff hlt]
  have := Nat.two_pow_pos i
  omega

/-! ## The normalized polynomials -/

/-- `Ŵ_i = W_i / W_i(e_i)`. The hat is normalization, not multilinear extension. -/
noncomputable def normVanishing (i : ℕ) : K[X] := C (vanishingAt i (basisVec i))⁻¹ * vanishing i

/-- `Ŵ_i(a)`, computed from the product. -/
def normVanishingAt (i : ℕ) (a : K) : K := vanishingAt i a * (vanishingAt i (basisVec i))⁻¹

/-- `normVanishingAt` evaluates `normVanishing`. -/
@[simp] theorem eval_normVanishing (i : ℕ) (a : K) :
    (normVanishing i).eval a = normVanishingAt i a := by
  rw [normVanishing, normVanishingAt, eval_mul, eval_C, eval_vanishing, mul_comm]

/-- `Ŵ_i(e_i) = 1` for `i < 64`. -/
theorem normVanishingAt_basisVec {i : ℕ} (hi : i < 64) : normVanishingAt i (basisVec i) = 1 :=
  mul_inv_cancel₀ (vanishingAt_basisVec_ne_zero hi)

/-- `deg Ŵ_i = 2^i` for `i < 64`. -/
theorem natDegree_normVanishing {i : ℕ} (hi : i < 64) :
    (normVanishing i).natDegree = 2 ^ i := by
  rw [normVanishing, natDegree_C_mul (inv_ne_zero (vanishingAt_basisVec_ne_zero hi)),
    natDegree_vanishing]

/-- `Ŵ_i ≠ 0` for `i < 64`. -/
theorem normVanishing_ne_zero {i : ℕ} (hi : i < 64) : normVanishing i ≠ 0 := by
  intro h
  have := natDegree_normVanishing hi
  rw [h, natDegree_zero] at this
  exact (Nat.two_pow_pos i).ne this

/-- `Ŵ_0 = X`, since `e_0 = 1` and `W_0 = X`. -/
theorem normVanishing_zero : normVanishing 0 = X := by
  rw [normVanishing, vanishing_zero]
  simp [vanishingAt, basisVec_zero]

/-- `Ŵ_i` is additive on `K`. -/
theorem normVanishingAt_add (i : ℕ) (a b : K) :
    normVanishingAt i (a + b) = normVanishingAt i a + normVanishingAt i b := by
  rw [normVanishingAt, normVanishingAt, normVanishingAt, vanishingAt_add, add_mul]

end
end LeanVM.Protocol.Whir
