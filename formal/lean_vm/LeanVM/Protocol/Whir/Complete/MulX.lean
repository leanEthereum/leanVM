/-
  LeanVM.Protocol.Whir.Complete.MulX

  Multiplication by `X` in the novel basis (Annex D, `lem:mulx`): the honest prover's `mulXA`
  computes the novel-basis coefficients of `X` times a lane.
-/

module

public import LeanVM.Protocol.Whir.SubspaceAt
public import LeanVM.Prover.Ntt
public import Statement.Prover.Whir

/-!
# Multiplication by `X` in the novel basis

`X_c = ∏_{c_i = 1} Ŵ_i` (`novelAt`), and `Ŵ_i^2 = Ŵ_i + a_i Ŵ_(i+1)` with
`a_i = W_(i+1)(β_(i+1)) / W_i(β_i)^2` (`hat_sq`). With `A_t = a_0 ⋯ a_(t-1)` (`AK`, the prover's
`xmulConsts`, `xmulConsts_getD`), telescoping gives `x Ŵ_0 ⋯ Ŵ_(s-1) = Σ_(k<s) A_k Ŵ_k ⋯ Ŵ_(s-1) +
A_s Ŵ_s` (`telescope`), hence for `d` with `s` trailing ones

  `x X_d(x) = A_s X_(d+1)(x) + Σ_(k<s) A_k X_(d+1-2^k)(x)` (`x_mul_novelAt`).

Regrouped by the index of the result, this is the rule of `mul_x` (`crates/pcs/src/xmul.rs`):
`(X h)[0] = 0`, `(X h)[c] = A_t (h[c-1] + h[c+2^t-1])`, `t` the trailing zeros of `c`
(`trailingZeros`, `trailingZeros_two_pow_mul_odd`); `sum_mxE` is the identity
`Σ_c (X h)[c] X_c(x) = x Σ_d h[d] X_d(x)`, and `sum_mulXA` its form on the prover's tables.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Prover Finset

@[expose] public section

/-! ## The constants -/

/-- `a_i = W_(i+1)(β_(i+1)) / W_i(β_i)^2`. -/
noncomputable def aK (i : ℕ) : K :=
  vanishingAt (i + 1) (basisVec (i + 1)) * (vanishingAt i (basisVec i) * vanishingAt i (basisVec i))⁻¹

/-- `A_t = a_0 ⋯ a_(t-1)`. -/
noncomputable def AK : ℕ → K
  | 0 => 1
  | t + 1 => AK t * aK t

/-- `Ŵ_i^2 = Ŵ_i + a_i Ŵ_(i+1)`. -/
theorem hat_sq {i : ℕ} (hi : i + 1 < 64) (x : K) :
    normVanishingAt i x * normVanishingAt i x =
      normVanishingAt i x + aK i * normVanishingAt (i + 1) x := by
  have hr : vanishingAt i (basisVec i) ≠ 0 := vanishingAt_basisVec_ne_zero (by omega)
  have hr' : vanishingAt (i + 1) (basisVec (i + 1)) ≠ 0 := vanishingAt_basisVec_ne_zero hi
  simp only [normVanishingAt, aK]
  rw [vanishingAt_succ i x]
  field_simp
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (-(vanishingAt i x * vanishingAt i (basisVec i))) * h2

/-- `Ŵ_0(x) = x`. -/
theorem normVanishingAt_zero (x : K) : normVanishingAt 0 x = x := by
  simp [normVanishingAt, Enc.vanishingAt_zero_left, basisVec_zero]

/-- The prover's `subspaceRoot t` is `W_t(β_t)`. -/
theorem subspaceRoot_eq {t : ℕ} (ht : t < 64) : subspaceRoot t = vanishingAt t (basisVec t) :=
  Enc.vanRow_getD t ht t ht

/-- The prover's constants, built by the loop. -/
theorem foldl_xmul (n : ℕ) (hn : n ≤ 63) :
    (List.range n).foldl (fun a t ↦
        a.push (a.getD t 1 * subspaceRoot (t + 1) * (subspaceRoot t * subspaceRoot t)⁻¹)) #[1] =
      Array.ofFn (n := n + 1) fun t ↦ AK t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
    refine Array.ext (by simp) fun i h₁ h₂ ↦ ?_
    simp only [Array.size_push, Array.size_ofFn] at h₁
    rw [Array.getElem_push, Array.getElem_ofFn]
    split
    · rw [Array.getElem_ofFn]
    · have hi : i = n + 1 := by simp at *; omega
      subst hi
      have hn : n < n + 1 := by omega
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hn, ↓reduceDIte,
        Option.getD_some]
      rw [subspaceRoot_eq (by omega), subspaceRoot_eq (by omega), AK, aK]
      ring

/-- **The prover's `xmulConsts` are the `A_t`.** -/
theorem xmulConsts_getD {t : ℕ} (ht : t < 64) : xmulConsts.getD t 0 = AK t := by
  rw [show xmulConsts = Array.ofFn (n := 63 + 1) fun t ↦ AK t from foldl_xmul 63 le_rfl,
    Enc.getD_ofFn _ _ _ (by omega)]

/-! ## Trailing zeros -/

/-- `2^v (2o + 1) − 1` read bit by bit: ones below `v`, then `o`'s bits shifted. -/
private theorem testBit_pred (v o i : ℕ) :
    (2 ^ v * (2 * o + 1) - 1).testBit i = if i < v then true else (2 * o).testBit (i - v) := by
  have : 2 ^ v * (2 * o + 1) - 1 = 2 ^ v * (2 * o) + (2 ^ v - 1) := by
    have := Nat.one_le_two_pow (n := v); rw [mul_add, mul_one]; omega
  rw [this, Nat.testBit_two_pow_mul_add _ (by have := Nat.one_le_two_pow (n := v); omega),
    Nat.testBit_two_pow_sub_one]
  split <;> simp_all

/-- **The trailing zeros** of `2^v (2o + 1)` are `v`. -/
theorem trailingZeros_two_pow_mul_odd (v o : ℕ) : trailingZeros (2 ^ v * (2 * o + 1)) = v := by
  have hx : 2 ^ v * (2 * o + 1) ^^^ (2 ^ v * (2 * o + 1) - 1) = 2 ^ (v + 1) - 1 := by
    refine Nat.eq_of_testBit_eq fun i ↦ ?_
    rw [Nat.testBit_xor, testBit_pred, Nat.testBit_two_pow_sub_one,
      show 2 ^ v * (2 * o + 1) = 2 ^ v * (2 * o + 1) + 0 from rfl,
      Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos v)]
    rcases lt_trichotomy i v with h | rfl | h
    · simp [h, Nat.lt_succ_of_lt h]
    · simp
    · have h1 : ¬ i < v := by omega
      have h2 : ¬ i < v + 1 := by omega
      obtain ⟨j, hj⟩ : ∃ j, i - v = j + 1 := ⟨i - v - 1, by omega⟩
      simp only [h1, h2, ite_false, decide_false]
      rw [hj]
      rw [show 2 * o + 1 = 2 ^ 1 * o + 1 by ring, show 2 * o = 2 ^ 1 * o + 0 by ring,
        Nat.testBit_two_pow_mul_add _ (by norm_num), Nat.testBit_two_pow_mul_add _ (by norm_num)]
      simp
  rw [trailingZeros, hx, Nat.log2_eq_iff (by have := Nat.one_le_two_pow (n := v + 1); omega)]
  constructor
  · rw [pow_succ]; have := Nat.one_le_two_pow (n := v); omega
  · have := Nat.one_le_two_pow (n := v + 1); omega

/-! ## The novel basis on bits -/

/-- `X_(2^m a + r) = X_(2^m a) X_r` for `r < 2^m`. -/
theorem novelAt_two_pow_mul_add (m a r : ℕ) (hr : r < 2 ^ m) (x : K) :
    novelAt (2 ^ m * a + r) x = novelAt (2 ^ m * a) x * novelAt r x := by
  simp only [novelAt, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [Nat.testBit_two_pow_mul_add _ hr,
    show 2 ^ m * a = 2 ^ m * a + 0 from rfl, Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos m)]
  by_cases hi : i < m
  · simp [hi]
  · have : r.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, this]

/-- `X_(2^s − 2^k)(x) = Ŵ_k(x) ⋯ Ŵ_(s−1)(x)` for `k ≤ s ≤ 64`. -/
theorem novelAt_two_pow_sub (k s : ℕ) (hks : k ≤ s) (hs : s ≤ 64) (x : K) :
    novelAt (2 ^ s - 2 ^ k) x = ∏ i ∈ Ico k s, normVanishingAt i x := by
  have hbits : ∀ i, (2 ^ s - 2 ^ k).testBit i = decide (k ≤ i ∧ i < s) := by
    intro i
    have : 2 ^ s - 2 ^ k = (2 ^ (s - k) - 1) * 2 ^ k := by
      rw [Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel hks]
    rw [this, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases h : k ≤ i
    · simp only [h, decide_true, Bool.true_and, true_and]
      exact decide_eq_decide.mpr (by omega)
    · simp [h]
  have hsub : Ico k s ⊆ range 64 := fun i hi ↦ by
    rw [mem_Ico] at hi; rw [mem_range]; omega
  rw [novelAt, ← prod_subset hsub]
  · refine prod_congr rfl fun i hi ↦ ?_
    rw [mem_Ico] at hi
    simp [hbits, hi.1, hi.2]
  · intro i _ hi
    rw [mem_Ico] at hi
    simp only [hbits]
    split
    · next h => exact absurd (by simpa using h) hi
    · rfl

/-! ## Telescoping -/

/-- `x Ŵ_0 ⋯ Ŵ_(s−1) = Σ_(k<s) A_k Ŵ_k ⋯ Ŵ_(s−1) + A_s Ŵ_s`. -/
theorem telescope (x : K) : ∀ s, s ≤ 63 →
    x * ∏ i ∈ range s, normVanishingAt i x =
      ∑ k ∈ range s, AK k * ∏ i ∈ Ico k s, normVanishingAt i x + AK s * normVanishingAt s x
  | 0, _ => by simp [AK, normVanishingAt_zero]
  | s + 1, hs => by
    have ih := telescope x s (by omega)
    have hstep : ∀ k ∈ range s, AK k * ∏ i ∈ Ico k (s + 1), normVanishingAt i x =
        (AK k * ∏ i ∈ Ico k s, normVanishingAt i x) * normVanishingAt s x := by
      intro k hk
      rw [prod_Ico_succ_top (by simp at hk; omega)]
      ring
    have hsq := hat_sq (i := s) (by omega) x
    calc x * ∏ i ∈ range (s + 1), normVanishingAt i x
        = (x * ∏ i ∈ range s, normVanishingAt i x) * normVanishingAt s x := by
          rw [prod_range_succ]; ring
      _ = (∑ k ∈ range s, AK k * ∏ i ∈ Ico k s, normVanishingAt i x) * normVanishingAt s x +
            AK s * (normVanishingAt s x * normVanishingAt s x) := by rw [ih]; ring
      _ = _ := by
          rw [hsq, sum_range_succ, sum_congr rfl hstep, sum_mul, Nat.Ico_succ_singleton,
            prod_singleton, AK]
          ring

/-- Index arithmetic of `x_mul_novelAt`. -/
private theorem idx_split (s o k : ℕ) (hk : k ≤ s) :
    2 ^ s * (2 * o + 1) - 2 ^ k = 2 ^ (s + 1) * o + (2 ^ s - 2 ^ k) := by
  have h1 : 2 ^ k ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hk
  have e1 : 2 ^ s * (2 * o + 1) = 2 * (2 ^ s * o) + 2 ^ s := by ring
  have e2 : 2 ^ (s + 1) * o = 2 * (2 ^ s * o) := by ring
  rw [e1, e2]
  generalize 2 ^ s * o = Q at *
  generalize 2 ^ s = P at *
  generalize 2 ^ k = R at *
  omega

/-- **`x X_d(x)`** for `d + 1 = 2^s (2o + 1)`: `A_s X_(d+1)(x) + Σ_(k<s) A_k X_(d+1−2^k)(x)`. -/
theorem x_mul_novelAt (s o : ℕ) (hs : s ≤ 62) (x : K) :
    x * novelAt (2 ^ s * (2 * o + 1) - 1) x =
      AK s * novelAt (2 ^ s * (2 * o + 1)) x +
        ∑ k ∈ range s, AK k * novelAt (2 ^ s * (2 * o + 1) - 2 ^ k) x := by
  have hsplit : ∀ r, r < 2 ^ (s + 1) →
      novelAt (2 ^ (s + 1) * o + r) x = novelAt (2 ^ (s + 1) * o) x * novelAt r x :=
    fun r hr ↦ novelAt_two_pow_mul_add (s + 1) o r hr x
  have hlt : ∀ k, k ≤ s → 2 ^ s - 2 ^ k < 2 ^ (s + 1) := fun k _ ↦
    lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hsum : ∑ k ∈ range s, AK k * novelAt (2 ^ s * (2 * o + 1) - 2 ^ k) x =
      novelAt (2 ^ (s + 1) * o) x *
        ∑ k ∈ range s, AK k * ∏ i ∈ Ico k s, normVanishingAt i x := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    have hk' := (mem_range.mp hk).le
    rw [idx_split s o k hk', hsplit _ (hlt k hk'), novelAt_two_pow_sub k s hk' (by omega)]
    ring
  have e1 : 2 ^ s * (2 * o + 1) - 1 = 2 ^ (s + 1) * o + (2 ^ s - 2 ^ 0) := by
    rw [← idx_split s o 0 (Nat.zero_le _), pow_zero]
  have e2 : 2 ^ s * (2 * o + 1) = 2 ^ (s + 1) * o + (2 ^ (s + 1) - 2 ^ s) := by
    have e' : 2 ^ s * (2 * o + 1) = 2 ^ (s + 1) * o + 2 ^ s := by ring
    have : 2 ^ (s + 1) - 2 ^ s = 2 ^ s := by rw [pow_succ]; omega
    rw [e', this]
  have hlt' : 2 ^ (s + 1) - 2 ^ s < 2 ^ (s + 1) := by
    have := Nat.two_pow_pos s; omega
  rw [hsum, e1, hsplit _ (hlt 0 (Nat.zero_le _)), e2, hsplit _ hlt',
    novelAt_two_pow_sub 0 s (Nat.zero_le _) (by omega),
    novelAt_two_pow_sub s (s + 1) (by omega) (by omega), ← range_eq_Ico, Nat.Ico_succ_singleton,
    prod_singleton, mul_left_comm, telescope x s (by omega)]
  ring

/-! ## Regrouping by the result's index -/

/-- Every `n ≥ 1` is `2^v (2o + 1)`. -/
theorem exists_two_pow_mul_odd {n : ℕ} (hn : n ≠ 0) : ∃ v o, n = 2 ^ v * (2 * o + 1) := by
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  obtain ⟨o, rfl⟩ := hm
  exact ⟨v, o, by ring⟩

/-- The trailing zeros of a multiple of `2^w` are at least `w`. -/
theorem le_trailingZeros {w m : ℕ} (hm : m ≠ 0) : w ≤ trailingZeros (2 ^ w * m) := by
  obtain ⟨a, b, rfl⟩ := exists_two_pow_mul_odd hm
  rw [← mul_assoc, ← pow_add, trailingZeros_two_pow_mul_odd]
  omega

/-- **`x X_d(x)`**, by the trailing zeros of `d + 1`. -/
theorem x_mul_novelAt' (d : ℕ) (hd : d + 1 ≤ 2 ^ 62) (x : K) :
    x * novelAt d x = AK (trailingZeros (d + 1)) * novelAt (d + 1) x +
      ∑ k ∈ range (trailingZeros (d + 1)), AK k * novelAt (d + 1 - 2 ^ k) x := by
  obtain ⟨s, o, ho⟩ := exists_two_pow_mul_odd (n := d + 1) (by omega)
  have hs : s ≤ 62 := by
    by_contra h
    have : 2 ^ 63 ≤ d + 1 := by
      rw [ho]
      calc 2 ^ 63 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 2 ^ s * (2 * o + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have : 2 ^ 62 < 2 ^ 63 := by norm_num
    omega
  have hd' : d = 2 ^ s * (2 * o + 1) - 1 := by omega
  rw [ho, trailingZeros_two_pow_mul_odd]
  nth_rewrite 1 [hd']
  exact x_mul_novelAt s o hs x

/-- `(X h)[c]`, the prover's rule (`mul_x`, `crates/pcs/src/xmul.rs`). -/
noncomputable def mxE (h : ℕ → E) (c : ℕ) : E :=
  if c = 0 then 0 else ofK (AK (trailingZeros c)) * (h (c - 1) + h (c + 2 ^ trailingZeros c - 1))

/-- The index `c` reads beyond itself: `c + 2^t − 1`. -/
def farIdx (c : ℕ) : ℕ := c + 2 ^ trailingZeros c - 1

/-- The pairs `(d, k)`, `k` below the trailing zeros of `d + 1`, are the indices `c ≥ 1` by
`c = d + 1 − 2^k`, `d = c + 2^(tz c) − 1`, `k = tz c`. -/
private theorem pair_facts (d k : ℕ) (hk : k < trailingZeros (d + 1)) :
    d + 1 - 2 ^ k ≠ 0 ∧ trailingZeros (d + 1 - 2 ^ k) = k ∧ farIdx (d + 1 - 2 ^ k) = d := by
  obtain ⟨s, o, ho⟩ := exists_two_pow_mul_odd (n := d + 1) (by omega)
  rw [ho, trailingZeros_two_pow_mul_odd] at hk
  obtain ⟨j, rfl⟩ : ∃ j, s = k + 1 + j := ⟨s - k - 1, by omega⟩
  -- `d + 1 − 2^k = 2^k (2 (2^j (2o + 1)) − 1) = 2^k (2 o' + 1)`.
  have hpos : 1 ≤ 2 ^ j * (2 * o + 1) := Nat.mul_pos (Nat.two_pow_pos j) (by omega)
  have hc : d + 1 - 2 ^ k = 2 ^ k * (2 * (2 ^ j * (2 * o + 1) - 1) + 1) := by
    rw [ho, pow_add, pow_add, pow_one]
    have e : 2 ^ k * 2 * 2 ^ j * (2 * o + 1) = 2 ^ k * (2 * (2 ^ j * (2 * o + 1))) := by ring
    rw [e]
    generalize 2 ^ j * (2 * o + 1) = M at *
    have : 2 * (M - 1) + 1 = 2 * M - 1 := by omega
    rw [this, Nat.mul_sub, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; exact Nat.mul_ne_zero (Nat.two_pow_pos k).ne' (by omega)
  · rw [hc, trailingZeros_two_pow_mul_odd]
  · rw [farIdx, hc, trailingZeros_two_pow_mul_odd, ← hc]
    have : 2 ^ k ≤ d + 1 := by
      rw [ho]
      calc 2 ^ k ≤ 2 ^ (k + 1 + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- Conversely, an index `c ≥ 1` comes from the pair `(c + 2^(tz c) − 1, tz c)`. -/
private theorem index_facts {c : ℕ} (hc : c ≠ 0) :
    trailingZeros c < trailingZeros (farIdx c + 1) ∧ farIdx c + 1 - 2 ^ trailingZeros c = c := by
  obtain ⟨v, o, rfl⟩ := exists_two_pow_mul_odd hc
  have hf : farIdx (2 ^ v * (2 * o + 1)) + 1 = 2 ^ (v + 1) * (o + 1) := by
    rw [farIdx, trailingZeros_two_pow_mul_odd]
    have := Nat.two_pow_pos v
    rw [pow_succ]
    have e : 2 ^ v * (2 * o + 1) + 2 ^ v = 2 ^ v * 2 * (o + 1) := by ring
    omega
  refine ⟨?_, ?_⟩
  · rw [hf, trailingZeros_two_pow_mul_odd]
    have := le_trailingZeros (w := v + 1) (m := o + 1) (by omega)
    omega
  · rw [hf, trailingZeros_two_pow_mul_odd, pow_succ]
    have e : 2 ^ v * 2 * (o + 1) = 2 ^ v * (2 * o + 1) + 2 ^ v := by ring
    omega

/-- **Multiplication by `X` in the novel basis** (Annex D, `lem:mulx`): for a lane `h` vanishing
from `N ≤ 2^62` on, `Σ_(c ≤ N) (X h)[c] X_c(x) = x Σ_(d < N) h[d] X_d(x)`. -/
theorem sum_mxE (h : ℕ → E) (N : ℕ) (hN : N ≤ 2 ^ 62) (hz : ∀ c, N ≤ c → h c = 0) (x : K) :
    ∑ c ∈ range (N + 1), mxE h c * ofK (novelAt c x) =
      ofK x * ∑ d ∈ range N, h d * ofK (novelAt d x) := by
  classical
  have hof : ∀ a b : K, ofK (a * b) = ofK a * ofK b := fun a b ↦ ofK_mul a b
  have hosum : ∀ (s : Finset ℕ) (f : ℕ → K), ofK (∑ k ∈ s, f k) = ∑ k ∈ s, ofK (f k) :=
    fun s f ↦ map_sum (algebraMap K E) f s
  set e : ℕ → E := fun c ↦ ofK (novelAt c x) with he
  set A : ℕ → E := fun t ↦ ofK (AK t) with hA
  -- The right side, term by term.
  have hR : ofK x * ∑ d ∈ range N, h d * e d =
      ∑ d ∈ range N, A (trailingZeros (d + 1)) * h d * e (d + 1) +
        ∑ d ∈ range N, ∑ k ∈ range (trailingZeros (d + 1)), h d * (A k * e (d + 1 - 2 ^ k)) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun d hd ↦ ?_
    have hd' : d + 1 ≤ 2 ^ 62 := by have := mem_range.mp hd; omega
    have := congrArg ofK (x_mul_novelAt' d hd' x)
    rw [hof, ofK_add, hof, hosum] at this
    simp only [hof] at this
    simp only [he, hA]
    rw [mul_left_comm, this, mul_add, mul_sum]
    ring
  -- The left side, split along the two reads.
  have hsplit : ∀ c, mxE h c * e c = (if c = 0 then 0 else A (trailingZeros c) * h (c - 1) * e c) +
      (if c = 0 then 0 else A (trailingZeros c) * h (farIdx c) * e c) := by
    intro c
    by_cases hc : c = 0
    · simp [mxE, hc]
    · simp only [mxE, hc, ite_false, farIdx]; ring
  rw [sum_congr rfl fun c _ ↦ hsplit c, sum_add_distrib, sum_range_succ', hR]
  simp only [Nat.succ_ne_zero, ite_false, ite_true, add_zero, Nat.add_sub_cancel]
  congr 1
  -- The far reads, pair by pair.
  have hfilt : ∑ c ∈ range (N + 1), (if c = 0 then 0 else A (trailingZeros c) * h (farIdx c) * e c) =
      ∑ c ∈ (range (N + 1)).filter (fun c ↦ c ≠ 0 ∧ farIdx c < N),
        A (trailingZeros c) * h (farIdx c) * e c := by
    rw [sum_filter]
    refine sum_congr rfl fun c _ ↦ ?_
    by_cases hc : c = 0
    · simp [hc]
    · by_cases hf : farIdx c < N
      · simp [hc, hf]
      · simp [hc, hf, hz _ (not_lt.mp hf)]
  rw [hfilt, sum_sigma']
  refine (sum_bij' (fun p _ ↦ p.1 + 1 - 2 ^ p.2) (fun c _ ↦ ⟨farIdx c, trailingZeros c⟩)
    ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨d, k⟩ hp
    simp only [mem_sigma, mem_range] at hp
    obtain ⟨h1, h2, h3⟩ := pair_facts d k hp.2
    simp only [mem_filter, mem_range]
    have := Nat.one_le_two_pow (n := k)
    exact ⟨by omega, h1, by rw [h3]; exact hp.1⟩
  · intro c hc
    simp only [mem_filter, mem_range] at hc
    simp only [mem_sigma, mem_range]
    exact ⟨hc.2.2, (index_facts hc.2.1).1⟩
  · rintro ⟨d, k⟩ hp
    simp only [mem_sigma, mem_range] at hp
    obtain ⟨-, h2, h3⟩ := pair_facts d k hp.2
    simp [h2, h3]
  · intro c hc
    simp only [mem_filter, mem_range] at hc
    exact (index_facts hc.2.1).2
  · rintro ⟨d, k⟩ hp
    simp only [mem_sigma, mem_range] at hp
    obtain ⟨-, h2, h3⟩ := pair_facts d k hp.2
    simp only [h2, h3]
    ring

end
end LeanVM.Protocol.Whir.Complete
