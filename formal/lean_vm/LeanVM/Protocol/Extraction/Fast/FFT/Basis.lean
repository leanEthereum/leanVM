module

public import LeanVM.Protocol.Extraction.Novel
public import Mathlib.Tactic.LinearCombination

/-!
# Monomial ↔ novel basis over `K` in `O(N log² N)`

The novel basis `X_j = ∏_{bit i of j} Ŵ_i` (`novelPoly`, `LeanVM.Extraction.NovelProofs`) of the
polynomials of fewer than `2^J` coefficients, and the conversions (Lin, Chung and Han, FOCS 2014,
§III; Gao and Mateer's divide-by-subspace-polynomial recursion):

* `toNovelRec tab a` (monomial → novel): a polynomial `a` of `2^(i+1)` coefficients is
  `a = q·W_i + r` (`W_i = vanishing i`, monic of degree `2^i`, `deg r, deg q < 2^i`), so
  `a = r + (β_i·q)·Ŵ_i` with `β_i = W_i(x^i)`, and its novel coefficients are those of `r`
  followed by those of `β_i·q` (`X_{2^i + k} = Ŵ_i·X_k`, `k < 2^i`);
* `fromNovelRec tab c` (novel → monomial): the converse, `a = r + (β_i^{-1}·q̂)·W_i`.

`W_i` is **linearized**, `W_i = Σ_{t≤i} s_{i,t}·X^(2^t)`, `s_{i,i} = 1` (`linData`, from
`W_{i+1} = W_i² + β_i·W_i`, the squaring additive in characteristic two), so the division of
`2^(i+1)` coefficients by `W_i` takes two blocks of `2^(i−1)` quotient coefficients read off
the top (`W_i − X^(2^i)` has degree `2^(i−1)`) and `≈ (i+1)·2^i` products in all; a conversion
of `N = 2^J` coefficients `≈ N·J(J+1)/4` products. The table of the `s_{i,·}` and `β_i`
(`tableUpTo J`, `tableInvUpTo J` with `β_i^{-1}`) is built once per conversion, `O(J²)`
products and `J` inversions.

Arrays are built stage by stage (`Array.ofFn`, `++`); the recursions are structural (on the
table, on the number of terms).

Proved, for `J ≤ 64` (`N = 2^J`, `polyN N a = Σ_{d<N} a_d·X^d`, `novelSum N c = Σ_{t<N} c_t·X_t`):
* `novelSum_toNovel`: `novelSum N (toNovel J a) = polyN N a`, of size `N` (`size_toNovel`);
* `polyN_fromNovel`: `polyN N (fromNovel J c) = novelSum N c`, of size `N`;
* `fromNovel_toNovel`, `toNovel_fromNovel`: inverse to each other (on the first `N` entries);
* `eval_novelSum`: `novelSum N c` at `x_v` is the `Σ_t c_t·X_t(x_v)` of `novelFwd_getD`.

The facts about `vanishing` (`vanishing_succ`) are those of `Subspace.lean` (private there),
reproved.
-/

namespace LeanVM.Extraction.Fast.FFT

open LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Words LeanVM.Extraction.Subspace
  LeanVM.Extraction.NovelProofs Polynomial

public section

attribute [local simp] LeanVM.Extraction.Words.ofBits_zero

/-! ## Definitions -/

/-- `Σ_{t<n} s_{o+t}·a^(2^t)`, by squarings. -/
@[expose] def evalLinFrom (s : Array K) : ℕ → ℕ → K → K
  | 0, _, _ => 0
  | n + 1, o, a => s.getD o 0 * a + evalLinFrom s n (o + 1) (a * a)

/-- The linearized polynomial `Σ_t s_t·X^(2^t)` at `a`. -/
@[expose] def evalLin (s : Array K) (a : K) : K := evalLinFrom s s.size 0 a

/-- `W_{i+1} = W_i² + β_i·W_i` on the linearized coefficients: entry `t` is
`s_{t−1}² + β·s_t`. -/
@[expose] def linStep (s : Array K) (β : K) : Array K :=
  Array.ofFn fun t : Fin (s.size + 1) ↦
    (if t.val = 0 then 0 else s.getD (t.val - 1) 0 * s.getD (t.val - 1) 0) + β * s.getD t.val 0

/-- The linearized coefficients of `W_i` and `β_i = W_i(x^i)`. -/
@[expose] def linData : ℕ → Array K × K
  | 0 => (#[1], evalLin #[1] (K.ofBits 1))
  | i + 1 =>
    let d := linData i
    let s := linStep d.1 d.2
    (s, evalLin s (K.ofBits (2 ^ (i + 1))))

/-- The levels `J − 1, …, 0`'s `(s_{i,·}, β_i)`, each from the previous one. -/
@[expose] def tableUpTo : ℕ → List (Array K × K)
  | 0 => []
  | J + 1 =>
    match tableUpTo J with
    | [] => [linData 0]
    | d :: rest =>
      let s := linStep d.1 d.2
      (s, evalLin s (K.ofBits (2 ^ J))) :: d :: rest

/-- The levels `J − 1, …, 0`'s `(s_{i,·}, β_i^{-1})`. -/
@[expose] def tableInvUpTo (J : ℕ) : List (Array K × K) :=
  (tableUpTo J).map fun d ↦ (d.1, d.2⁻¹)

/-- `Σ_{t<T, 2^t ≤ d, d − 2^t < n} s_t·q_{d−2^t}`: coefficient `d` of `q·Σ_{t<T} s_t·X^(2^t)`
for `q` of `n` coefficients. -/
@[expose] def linCoeff (s q : Array K) (n d : ℕ) : ℕ → K
  | 0 => 0
  | t + 1 => linCoeff s q n d t +
      if 2 ^ t ≤ d ∧ d - 2 ^ t < n then s.getD t 0 * q.getD (d - 2 ^ t) 0 else 0

/-- The quotient of `a` (`2^(i+1)` coefficients) by `X^(2^i) + Σ_{t<i} s_t·X^(2^t)`: its top
`2^i − h` coefficients (`h = 2^i / 2`) read off `a`, then its low `h` through them. -/
@[expose] def divQuot (s : Array K) (i : ℕ) (a : Array K) : Array K :=
  let H := 2 ^ i
  let h := H / 2
  let qtop := Array.ofFn fun e : Fin (H - h) ↦ a.getD (H + h + e.val) 0
  let qlo := Array.ofFn fun e : Fin h ↦
    a.getD (H + e.val) 0 - linCoeff s qtop (H - h) (H + e.val - h) i
  qlo ++ qtop

/-- The remainder, `a − q·Σ_{t<i} s_t·X^(2^t)` below `2^i`. -/
@[expose] def divRem (s : Array K) (i : ℕ) (a q : Array K) : Array K :=
  Array.ofFn fun e : Fin (2 ^ i) ↦ a.getD e.val 0 - linCoeff s q (2 ^ i) e.val i

/-- `(β·q_e)_{e<n}`. -/
@[expose] def scaleArr (n : ℕ) (β : K) (q : Array K) : Array K :=
  Array.ofFn fun e : Fin n ↦ β * q.getD e.val 0

/-- `(c_{o+e})_{e<n}`. -/
@[expose] def sliceArr (n o : ℕ) (c : Array K) : Array K :=
  Array.ofFn fun e : Fin n ↦ c.getD (o + e.val) 0

/-- `r + q·(X^(2^i) + Σ_{t<i} s_t·X^(2^t))` on `2^(i+1)` coefficients. -/
@[expose] def mulAddW (s : Array K) (i : ℕ) (r q : Array K) : Array K :=
  Array.ofFn fun d : Fin (2 * 2 ^ i) ↦
    (if d.val < 2 ^ i then r.getD d.val 0 else q.getD (d.val - 2 ^ i) 0) +
      linCoeff s q (2 ^ i) d.val i

/-- **Monomial → novel**, on the table of levels `i = |tab|, …, 0`: `2^(i+1)` coefficients
divided by `W_i`. -/
@[expose] def toNovelRec : List (Array K × K) → Array K → Array K
  | [], a => #[a.getD 0 0]
  | (s, β) :: tab, a =>
    let i := tab.length
    let q := divQuot s i a
    toNovelRec tab (divRem s i a q) ++ toNovelRec tab (scaleArr (2 ^ i) β q)

/-- **Novel → monomial**, on the table of levels with `β_i^{-1}`. -/
@[expose] def fromNovelRec : List (Array K × K) → Array K → Array K
  | [], c => #[c.getD 0 0]
  | (s, βinv) :: tab, c =>
    let i := tab.length
    let r := fromNovelRec tab (sliceArr (2 ^ i) 0 c)
    let qh := fromNovelRec tab (sliceArr (2 ^ i) (2 ^ i) c)
    mulAddW s i r (scaleArr (2 ^ i) βinv qh)

/-- The novel-basis coefficients of the polynomial with monomial coefficients `a_0, …, a_{2^J−1}`. -/
@[expose] def toNovel (J : ℕ) (a : Array K) : Array K := toNovelRec (tableUpTo J) a

/-- The monomial coefficients of `Σ_{t<2^J} c_t·X_t`. -/
@[expose] def fromNovel (J : ℕ) (c : Array K) : Array K := fromNovelRec (tableInvUpTo J) c

/-! ## Meanings -/

/-- `Σ_{d<n} a_d·X^d`. -/
@[expose] noncomputable def polyN (n : ℕ) (a : Array K) : K[X] :=
  ∑ d ∈ Finset.range n, C (a.getD d 0) * X ^ d

/-- `Σ_{t<n} c_t·X_t`, in the novel basis. -/
@[expose] noncomputable def novelSum (n : ℕ) (c : Array K) : K[X] :=
  ∑ t ∈ Finset.range n, C (c.getD t 0) * novelPoly t

/-- `Σ_{t<n} s_t·X^(2^t)`. -/
@[expose] noncomputable def linPoly (s : Array K) (n : ℕ) : K[X] :=
  ∑ t ∈ Finset.range n, C (s.getD t 0) * X ^ (2 ^ t)

/-! ## Arrays -/

theorem getD_ofFn {n p : ℕ} (f : Fin n → K) (hp : p < n) : (Array.ofFn f).getD p 0 = f ⟨p, hp⟩ := by
  simp [Array.getD, hp]

theorem getD_append (x y : Array K) (n : ℕ) :
    (x ++ y).getD n 0 = if n < x.size then x.getD n 0 else y.getD (n - x.size) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

theorem array_eq_of_getD {a b : Array K} (h : a.size = b.size)
    (hg : ∀ p < a.size, a.getD p 0 = b.getD p 0) : a = b := by
  apply Array.ext h
  intro p h1 h2
  have := hg p h1
  simp only [Array.getD, h1, h2, dite_true] at this
  exact this

/-! ## Polynomials -/

theorem coeff_polyN (n : ℕ) (a : Array K) (d : ℕ) :
    (polyN n a).coeff d = if d < n then a.getD d 0 else 0 := by
  rw [polyN, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem coeff_mul_linPoly (s q : Array K) (n d T : ℕ) :
    (polyN n q * linPoly s T).coeff d = linCoeff s q n d T := by
  induction T with
  | zero => simp [linPoly, linCoeff]
  | succ T ih =>
    rw [linPoly, Finset.sum_range_succ, ← linPoly, mul_add, coeff_add, ih, linCoeff,
      show polyN n q * (C (s.getD T 0) * X ^ 2 ^ T) = C (s.getD T 0) * polyN n q * X ^ 2 ^ T by ring,
      coeff_mul_X_pow', coeff_C_mul, coeff_polyN]
    by_cases h1 : 2 ^ T ≤ d
    · by_cases h2 : d - 2 ^ T < n
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]

theorem linCoeff_eq_zero (s q : Array K) {n d T : ℕ} (h : ∀ t < T, n + 2 ^ t ≤ d) :
    linCoeff s q n d T = 0 := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [linCoeff, ih fun t ht ↦ h t (by omega)]
    have := h T (by omega)
    rw [ite_eq_right (by omega), add_zero]

/-- The middle block's coefficients through the top quotient block. -/
theorem linCoeff_append (s : Array K) {qlo qtop : Array K} {H h d T : ℕ} (hH : H = 2 * h)
    (hlo : qlo.size = h) (hT : ∀ t < T, 2 ^ t ≤ h) (hd : H ≤ d) :
    linCoeff s (qlo ++ qtop) H d T = linCoeff s qtop (H - h) (d - h) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [linCoeff, linCoeff, ih fun t ht ↦ hT t (by omega)]
    congr 1
    have hT' := hT T (by omega)
    by_cases hc : d - 2 ^ T < H
    · rw [ite_eq_left ⟨by omega, hc⟩, ite_eq_left ⟨by omega, by omega⟩, getD_append, hlo,
        ite_eq_right (by omega), show d - 2 ^ T - h = d - h - 2 ^ T by omega]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## The novel basis as polynomials -/

theorem novelPoly_two_pow_add {i k : ℕ} (hk : k < 2 ^ i) :
    novelPoly (2 ^ i + k) = novelPoly (2 ^ i) * novelPoly k := by
  unfold novelPoly
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  have h := Nat.testBit_two_pow_mul_add 1 hk t
  rw [Nat.mul_one] at h
  rw [h, Nat.testBit_two_pow]
  by_cases ht : t < i
  · simp [ht, show i ≠ t by omega]
  · have hge : t ≥ i := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) hge))]
    by_cases hti : t = i
    · subst hti; simp
    · rw [Nat.testBit_lt_two_pow (show 1 < 2 ^ (t - i) from Nat.one_lt_two_pow (by omega))]
      simp [ht, Ne.symm hti]

theorem novelPoly_two_pow {i : ℕ} (hi : i < 64) :
    novelPoly (2 ^ i) = C (subspacePoly i (K.ofBits (2 ^ i)))⁻¹ * vanishing i := by
  unfold novelPoly
  simp only [Nat.testBit_two_pow]
  rw [Finset.prod_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_range.mpr hi) h

theorem eval_novelSum (n : ℕ) (c : Array K) (a : K) :
    (novelSum n c).eval a = ∑ t ∈ Finset.range n, c.getD t 0 * novelBasis t a := by
  simp [novelSum, eval_finsetSum, eval_novelPoly]

/-- The novel sum of two halves. -/
theorem novelSum_two_mul (i : ℕ) (c : Array K) :
    novelSum (2 * 2 ^ i) c = novelSum (2 ^ i) c +
      novelPoly (2 ^ i) * novelSum (2 ^ i) (Array.ofFn fun e : Fin (2 ^ i) ↦ c.getD (2 ^ i + e.val) 0) := by
  rw [novelSum, two_mul, Finset.sum_range_add, ← novelSum, novelSum, novelSum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [getD_ofFn _ (Finset.mem_range.mp he), novelPoly_two_pow_add (Finset.mem_range.mp he)]
  ring

theorem novelSum_append (i : ℕ) (x y : Array K) (hx : x.size = 2 ^ i) :
    novelSum (2 * 2 ^ i) (x ++ y) = novelSum (2 ^ i) x + novelPoly (2 ^ i) * novelSum (2 ^ i) y := by
  rw [novelSum_two_mul]
  congr 1
  · refine Finset.sum_congr rfl fun e he ↦ ?_
    rw [getD_append, ite_eq_left (by rw [hx]; exact Finset.mem_range.mp he)]
  · congr 1
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have he := Finset.mem_range.mp he
    rw [getD_ofFn _ he, getD_append, ite_eq_right (by omega), hx, Nat.add_sub_cancel_left]

/-! ## The subspace polynomials, linearized -/

private theorem vanishing_succ_split (i : ℕ) :
    vanishing (i + 1) = vanishing i * (vanishing i).comp (X + C (K.ofBits (2 ^ i))) := by
  rw [vanishing, pow_succ, mul_two, Finset.prod_range_add, vanishing, prod_comp]
  congr 1
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  rw [ofBits_two_pow_add (Finset.mem_range.mp hv)]
  simp only [add_comp, X_comp, C_comp, C_add]
  ring

private theorem char_two_cross (A B c : K[X]) :
    (A + B) * (A + B + c) = A * (A + c) + B * (B + c) := by
  linear_combination (A * B) * (CharTwo.two_eq_zero : (2 : K[X]) = 0)

/-- `W_{i+1} = W_i·(W_i + W_i(x^i))` (`Subspace.lean`'s `vanishing_comp_add_and_succ`, private
there, reproved). -/
theorem vanishing_succ (i : ℕ) :
    vanishing (i + 1) = vanishing i * (vanishing i + C (subspacePoly i (K.ofBits (2 ^ i)))) := by
  have step : ∀ i, (∀ a : K, (vanishing i).comp (X + C a) = vanishing i + C (subspacePoly i a)) →
      vanishing (i + 1) = vanishing i * (vanishing i + C (subspacePoly i (K.ofBits (2 ^ i)))) := by
    intro i h
    rw [vanishing_succ_split, h]
  have both : ∀ i, (∀ a : K, (vanishing i).comp (X + C a) = vanishing i + C (subspacePoly i a)) ∧
      vanishing (i + 1) =
        vanishing i * (vanishing i + C (subspacePoly i (K.ofBits (2 ^ i)))) := by
    intro i
    induction i with
    | zero =>
      refine ⟨fun a ↦ ?_, step 0 fun a ↦ ?_⟩ <;>
      · simp [vanishing_zero, subspacePoly]
    | succ i ih =>
      have hadd : ∀ a : K,
          (vanishing (i + 1)).comp (X + C a) = vanishing (i + 1) + C (subspacePoly (i + 1) a) := by
        intro a
        rw [← eval_vanishing (i + 1) a, ih.2, mul_comp, add_comp, C_comp, ih.1 a, eval_mul,
          eval_add, eval_C, eval_vanishing, C_mul, C_add]
        exact char_two_cross _ _ _
      exact ⟨hadd, step _ hadd⟩
  exact (both i).2

theorem evalLinFrom_eq (s : Array K) (n o : ℕ) (a : K) :
    evalLinFrom s n o a = ∑ t ∈ Finset.range n, s.getD (o + t) 0 * a ^ (2 ^ t) := by
  induction n generalizing o a with
  | zero => rfl
  | succ n ih =>
    show s.getD o 0 * a + evalLinFrom s n (o + 1) (a * a) = _
    rw [ih, Finset.sum_range_succ', add_comm]
    simp only [Nat.add_zero, pow_zero, pow_one]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun t _ ↦ ?_) rfl
    rw [show o + 1 + t = o + (t + 1) by omega, pow_succ, pow_mul, sq, mul_pow]

theorem evalLin_eq (s : Array K) (a : K) : evalLin s a = (linPoly s s.size).eval a := by
  rw [evalLin, evalLinFrom_eq, linPoly, eval_finsetSum]
  simp

theorem linPoly_sq (s : Array K) (n : ℕ) :
    linPoly s n ^ 2 = ∑ t ∈ Finset.range n, C (s.getD t 0 * s.getD t 0) * X ^ (2 ^ (t + 1)) := by
  induction n with
  | zero => simp [linPoly]
  | succ n ih =>
    rw [linPoly, Finset.sum_range_succ, ← linPoly, Finset.sum_range_succ, ← ih, add_sq,
      C_mul, pow_succ 2 n, pow_mul]
    linear_combination (linPoly s n * (C (s.getD n 0) * X ^ 2 ^ n)) *
      (CharTwo.two_eq_zero : (2 : K[X]) = 0)

theorem linPoly_linStep (s : Array K) (β : K) :
    linPoly (linStep s β) (s.size + 1) = linPoly s s.size ^ 2 + C β * linPoly s s.size := by
  have hg : ∀ t < s.size + 1, (linStep s β).getD t 0 =
      (if t = 0 then 0 else s.getD (t - 1) 0 * s.getD (t - 1) 0) + β * s.getD t 0 :=
    fun t ht ↦ by rw [linStep, getD_ofFn _ ht]
  rw [linPoly, Finset.sum_congr rfl fun t ht ↦ by rw [hg t (Finset.mem_range.mp ht)]]
  simp only [C_add, add_mul, Finset.sum_add_distrib]
  rw [linPoly_sq, Finset.sum_range_succ', Finset.sum_range_succ, linPoly, Finset.mul_sum]
  simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false, ite_true, C_0, zero_mul, add_zero]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (le_refl _)]
  simp only [Option.getD_none, mul_zero, C_0, zero_mul, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [C_mul, mul_assoc]

/-- The linearized form of `W_i`: `s_{i,·}` has `i + 1` entries, `s_{i,i} = 1`, and `β_i` is
`W_i(x^i)`. -/
theorem linData_spec (i : ℕ) :
    (linData i).1.size = i + 1 ∧ (linData i).1.getD i 0 = 1 ∧
      linPoly (linData i).1 (i + 1) = vanishing i ∧
      (linData i).2 = subspacePoly i (K.ofBits (2 ^ i)) := by
  have hβ : ∀ i, (linData i).1.size = i + 1 → linPoly (linData i).1 (i + 1) = vanishing i →
      ∀ x : Array K, x = (linData i).1 → evalLin x (K.ofBits (2 ^ i)) =
        subspacePoly i (K.ofBits (2 ^ i)) := by
    intro i hs hp x hx
    subst hx
    rw [evalLin_eq, hs, hp, eval_vanishing]
  induction i with
  | zero =>
    have h1 : (linData 0).1.size = 0 + 1 := rfl
    have h2 : linPoly (linData 0).1 (0 + 1) = vanishing 0 := by
      simp [linPoly, linData, vanishing_zero]
    refine ⟨h1, rfl, h2, ?_⟩
    exact hβ 0 h1 h2 _ rfl
  | succ i ih =>
    obtain ⟨hs, h1, hp, hb⟩ := ih
    have hs' : (linData (i + 1)).1.size = i + 1 + 1 := by
      simp [linData, linStep, hs]
    have hp' : linPoly (linData (i + 1)).1 (i + 1 + 1) = vanishing (i + 1) := by
      show linPoly (linStep (linData i).1 (linData i).2) (i + 1 + 1) = vanishing (i + 1)
      rw [← hs, linPoly_linStep, hs, hp, hb, vanishing_succ]
      ring
    refine ⟨hs', ?_, hp', hβ _ hs' hp' _ rfl⟩
    show (linStep (linData i).1 (linData i).2).getD (i + 1) 0 = 1
    rw [linStep, getD_ofFn _ (by omega)]
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, h1, mul_one]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp

theorem tableUpTo_eq (J : ℕ) : tableUpTo J = (List.range J).reverse.map linData := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [tableUpTo, ih, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons]
    cases J with
    | zero => rfl
    | succ J =>
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons]
      rfl

theorem tableUpTo_succ (J : ℕ) : tableUpTo (J + 1) = linData J :: tableUpTo J := by
  rw [tableUpTo_eq, tableUpTo_eq, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons]

theorem length_tableUpTo (J : ℕ) : (tableUpTo J).length = J := by
  rw [tableUpTo_eq, List.length_map, List.length_reverse, List.length_range]

theorem tableInvUpTo_succ (J : ℕ) :
    tableInvUpTo (J + 1) = ((linData J).1, (linData J).2⁻¹) :: tableInvUpTo J := by
  rw [tableInvUpTo, tableUpTo_succ, List.map_cons, ← tableInvUpTo]

theorem length_tableInvUpTo (J : ℕ) : (tableInvUpTo J).length = J := by
  rw [tableInvUpTo, List.length_map, length_tableUpTo]

/-- `W_i = X^(2^i) + Σ_{t<i} s_{i,t}·X^(2^t)`. -/
theorem vanishing_eq_linPoly (i : ℕ) :
    vanishing i = X ^ (2 ^ i) + linPoly (linData i).1 i := by
  obtain ⟨_, h1, hp, _⟩ := linData_spec i
  rw [← hp, linPoly, Finset.sum_range_succ, ← linPoly, h1, C_1, one_mul, add_comm]

theorem subspacePoly_basis_ne_zero' {i : ℕ} (hi : i < 64) :
    subspacePoly i (K.ofBits (2 ^ i)) ≠ 0 := subspacePoly_basis_ne_zero hi

/-! ## The division by `W_i` -/

/-- The level facts: `H = 2^i`, `h = H/2`, and the terms `t < i` of `W_i − X^H` have
`2^t ≤ h`. -/
theorem level_facts (i : ℕ) :
    (2 ^ i = 2 * (2 ^ i / 2) ∨ (2 ^ i = 1 ∧ 2 ^ i / 2 = 0)) ∧ ∀ t < i, 2 ^ t ≤ 2 ^ i / 2 := by
  cases i with
  | zero => exact ⟨Or.inr ⟨rfl, rfl⟩, fun t ht ↦ absurd ht (Nat.not_lt_zero _)⟩
  | succ i =>
    refine ⟨Or.inl (by rw [pow_succ]; omega), fun t ht ↦ ?_⟩
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The division step** of `toNovelRec`: `a = q·W_i + r` on `2^(i+1)` coefficients, for any
linearized `L = Σ_{t<i} s_t·X^(2^t)` in place of `W_i − X^(2^i)`. -/
theorem polyN_div (s a : Array K) (i : ℕ) :
    let H := 2 ^ i
    let h := H / 2
    let qtop := Array.ofFn fun e : Fin (H - h) ↦ a.getD (H + h + e.val) 0
    let qlo := Array.ofFn fun e : Fin h ↦
      a.getD (H + e.val) 0 - linCoeff s qtop (H - h) (H + e.val - h) i
    let q := qlo ++ qtop
    let r := Array.ofFn fun e : Fin H ↦ a.getD e.val 0 - linCoeff s q H e.val i
    q.size = H ∧ polyN (2 * H) a = polyN H q * (X ^ H + linPoly s i) + polyN H r := by
  intro H h qtop qlo q r
  obtain ⟨hH, hT⟩ := level_facts i
  have hqs : q.size = H := by
    simp only [q, qlo, qtop, Array.size_append, Array.size_ofFn]
    omega
  refine ⟨hqs, ?_⟩
  refine Polynomial.ext fun d ↦ ?_
  rw [coeff_add, mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_linPoly, coeff_polyN, coeff_polyN,
    coeff_polyN]
  have hq : ∀ e < H, q.getD e 0 = if e < h then qlo.getD e 0 else qtop.getD (e - h) 0 := by
    intro e _
    rw [getD_append]
    simp [qlo]
  by_cases hd : d < H
  · have : ¬ H ≤ d := by omega
    simp only [this, ite_false, zero_add, hd, ite_true, show d < 2 * H by omega]
    rw [show r.getD d 0 = a.getD d 0 - linCoeff s q H d i from getD_ofFn _ hd]
    ring
  · simp only [show H ≤ d by omega, ite_true, hd, ite_false, add_zero]
    by_cases hd2 : d < 2 * H
    · simp only [hd2, ite_true, show d - H < H by omega, ite_true]
      rw [hq _ (by omega)]
      by_cases hm : d - H < h
      · -- the low quotient block
        have hH2 : H = 2 * h := by rcases hH with hH | ⟨_, h0⟩ <;> omega
        rw [ite_eq_left hm, getD_ofFn _ hm, linCoeff_append s hH2 (by simp [qlo]) hT
          (by omega), show H + (d - H) - h = d - h by omega, show H + (d - H) = d by omega]
        ring
      · -- the top quotient block
        rw [ite_eq_right hm, getD_ofFn _ (by omega), linCoeff_eq_zero s q fun t ht ↦ ?_,
          show H + h + (d - H - h) = d by omega, add_zero]
        have := hT t ht
        omega
    · simp only [hd2, ite_false, show ¬ d - H < H by omega]
      rw [linCoeff_eq_zero s q fun t ht ↦ ?_]
      · ring
      · have := hT t ht
        omega

theorem polyN_divQuot (s a : Array K) (i : ℕ) :
    (divQuot s i a).size = 2 ^ i ∧
      polyN (2 * 2 ^ i) a = polyN (2 ^ i) (divQuot s i a) * (X ^ 2 ^ i + linPoly s i) +
        polyN (2 ^ i) (divRem s i a (divQuot s i a)) :=
  polyN_div s a i

/-- The product step of `fromNovelRec`. -/
theorem polyN_mulAddW (s : Array K) (i : ℕ) (r q : Array K) :
    polyN (2 * 2 ^ i) (mulAddW s i r q) = polyN (2 ^ i) r + polyN (2 ^ i) q * (X ^ 2 ^ i + linPoly s i) := by
  obtain ⟨_, hT⟩ := level_facts i
  refine Polynomial.ext fun d ↦ ?_
  rw [coeff_add, mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_linPoly, coeff_polyN,
    coeff_polyN, coeff_polyN]
  by_cases hd : d < 2 * 2 ^ i
  · rw [ite_eq_left hd, mulAddW, getD_ofFn _ hd]
    by_cases hd1 : d < 2 ^ i
    · simp [hd1, show ¬ 2 ^ i ≤ d by omega]
    · simp only [hd1, ite_false, show 2 ^ i ≤ d by omega, ite_true, show d - 2 ^ i < 2 ^ i by omega,
        zero_add]
  · rw [ite_eq_right hd, linCoeff_eq_zero _ _ fun t ht ↦ ?_]
    · simp [show ¬ d < 2 ^ i by omega, show ¬ d - 2 ^ i < 2 ^ i by omega]
    · have := hT t ht
      omega

/-! ## The conversions are correct -/

theorem polyN_scaleArr (n : ℕ) (β : K) (q : Array K) :
    polyN n (scaleArr n β q) = C β * polyN n q := by
  rw [polyN, polyN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [scaleArr, getD_ofFn _ (Finset.mem_range.mp he), C_mul, mul_assoc]

theorem size_scaleArr (n : ℕ) (β : K) (q : Array K) : (scaleArr n β q).size = n := Array.size_ofFn

/-- **Monomial → novel is correct.** -/
theorem toNovel_spec {J : ℕ} (hJ : J ≤ 64) (a : Array K) :
    (toNovel J a).size = 2 ^ J ∧ novelSum (2 ^ J) (toNovel J a) = polyN (2 ^ J) a := by
  induction J generalizing a with
  | zero =>
    refine ⟨rfl, ?_⟩
    simp [toNovel, tableUpTo, toNovelRec, novelSum, polyN, novelPoly]
  | succ J ih =>
    have ih' := fun a ↦ ih (by omega) a
    simp only [toNovel] at ih' ⊢
    rw [tableUpTo_succ, toNovelRec]
    simp only [length_tableUpTo]
    obtain ⟨_, hdiv⟩ := polyN_divQuot (linData J).1 a J
    generalize divQuot (linData J).1 J a = q at hdiv ⊢
    obtain ⟨hr1, hr2⟩ := ih' (divRem (linData J).1 J a q)
    obtain ⟨hq1, hq2⟩ := ih' (scaleArr (2 ^ J) (linData J).2 q)
    refine ⟨by rw [Array.size_append, hr1, hq1, pow_succ]; ring, ?_⟩
    rw [pow_succ, mul_comm, novelSum_append J _ _ hr1, hr2, hq2, hdiv, polyN_scaleArr,
      novelPoly_two_pow (by omega), (linData_spec J).2.2.2, vanishing_eq_linPoly]
    have hne := subspacePoly_basis_ne_zero' (i := J) (by omega)
    rw [add_comm (polyN (2 ^ J) q * _)]
    congr 1
    rw [show C (subspacePoly J (K.ofBits (2 ^ J)))⁻¹ * (X ^ 2 ^ J + linPoly (linData J).1 J) *
        (C (subspacePoly J (K.ofBits (2 ^ J))) * polyN (2 ^ J) q) =
        C ((subspacePoly J (K.ofBits (2 ^ J)))⁻¹ * subspacePoly J (K.ofBits (2 ^ J))) *
          (polyN (2 ^ J) q * (X ^ 2 ^ J + linPoly (linData J).1 J)) by rw [C_mul]; ring,
      inv_mul_cancel₀ hne, C_1, one_mul]

/-- **Novel → monomial is correct.** -/
theorem fromNovel_spec {J : ℕ} (hJ : J ≤ 64) (c : Array K) :
    (fromNovel J c).size = 2 ^ J ∧ polyN (2 ^ J) (fromNovel J c) = novelSum (2 ^ J) c := by
  induction J generalizing c with
  | zero =>
    refine ⟨rfl, ?_⟩
    simp [fromNovel, tableInvUpTo, tableUpTo, fromNovelRec, novelSum, polyN, novelPoly]
  | succ J ih =>
    have ih' := fun c ↦ ih (by omega) c
    simp only [fromNovel] at ih' ⊢
    rw [tableInvUpTo_succ, fromNovelRec]
    simp only [length_tableInvUpTo]
    obtain ⟨_, hr2⟩ := ih' (sliceArr (2 ^ J) 0 c)
    obtain ⟨_, hq2⟩ := ih' (sliceArr (2 ^ J) (2 ^ J) c)
    refine ⟨by rw [mulAddW, Array.size_ofFn, pow_succ, mul_comm], ?_⟩
    have hlo : novelSum (2 ^ J) (sliceArr (2 ^ J) 0 c) = novelSum (2 ^ J) c := by
      refine Finset.sum_congr rfl fun e he ↦ ?_
      rw [sliceArr, getD_ofFn _ (Finset.mem_range.mp he), Nat.zero_add]
    rw [pow_succ, mul_comm, novelSum_two_mul, ← hlo, ← hr2, show (Array.ofFn fun e : Fin (2 ^ J) ↦
      c.getD (2 ^ J + e.val) 0) = sliceArr (2 ^ J) (2 ^ J) c from rfl, ← hq2,
      novelPoly_two_pow (by omega), ← (linData_spec J).2.2.2, polyN_mulAddW, polyN_scaleArr,
      vanishing_eq_linPoly]
    ring

/-! ## Inverse to each other -/

theorem polyN_injective {n : ℕ} {a b : Array K} (ha : a.size = n) (hb : b.size = n)
    (h : polyN n a = polyN n b) : a = b := by
  apply array_eq_of_getD (by rw [ha, hb])
  intro p hp
  have := congrArg (fun P ↦ P.coeff p) h
  simp only [coeff_polyN, show p < n by omega, ite_true] at this
  exact this

/-- The novel coefficients are unique: their evaluations on `U_J` determine them (`novelInv`). -/
theorem novelSum_injective {J : ℕ} (hJ : J ≤ 64) {c c' : Array K} (hc : c.size = 2 ^ J)
    (hc' : c'.size = 2 ^ J) (h : novelSum (2 ^ J) c = novelSum (2 ^ J) c') : c = c' := by
  set y := Array.ofFn fun v : Fin (2 ^ J) ↦ (novelSum (2 ^ J) c).eval (K.ofBits v.val)
  have hofn : ∀ d : Array K, d.size = 2 ^ J →
      (Array.ofFn fun j : Fin (2 ^ J) ↦ d.getD j.val 0) = d := by
    intro d hd
    apply array_eq_of_getD (by rw [Array.size_ofFn, hd])
    intro p hp
    rw [Array.size_ofFn] at hp
    rw [getD_ofFn _ hp]
  have e1 := novelInv_eval hJ (fun j ↦ c.getD j 0) y Array.size_ofFn fun v hv ↦ by
    rw [getD_ofFn _ hv, eval_novelSum]
  have e2 := novelInv_eval hJ (fun j ↦ c'.getD j 0) y Array.size_ofFn fun v hv ↦ by
    rw [getD_ofFn _ hv, h, eval_novelSum]
  rw [← hofn c hc, ← hofn c' hc', ← e1, ← e2]

/-- **Round trip**: monomial → novel → monomial is the identity on `2^J` coefficients. -/
theorem fromNovel_toNovel {J : ℕ} (hJ : J ≤ 64) (a : Array K) (ha : a.size = 2 ^ J) :
    fromNovel J (toNovel J a) = a :=
  polyN_injective (fromNovel_spec hJ _).1 ha
    ((fromNovel_spec hJ _).2.trans (toNovel_spec hJ a).2)

/-- **Round trip**: novel → monomial → novel is the identity on `2^J` coefficients. -/
theorem toNovel_fromNovel {J : ℕ} (hJ : J ≤ 64) (c : Array K) (hc : c.size = 2 ^ J) :
    toNovel J (fromNovel J c) = c :=
  novelSum_injective hJ (toNovel_spec hJ _).1 hc
    ((toNovel_spec hJ _).2.trans (fromNovel_spec hJ c).2)

end

end LeanVM.Extraction.Fast.FFT
