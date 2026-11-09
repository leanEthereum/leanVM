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

end
end LeanVM.Protocol.Whir.Complete
