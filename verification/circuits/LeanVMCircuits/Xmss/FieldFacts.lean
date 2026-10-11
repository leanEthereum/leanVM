module

public import LeanVMCircuits.Rec.Field
public import LeanVMCircuits.Xmss.Circuit

@[expose] public section

/-!
# Powers of `x` in `K` behind the digit sum

The encoding's digits sum to 195 because the circuit holds the product of `x^(2^k)` over the digit bits of weight
`2^k` to `targetWord`. Here: the word `2` is `x`, the weight factors `x^(2^k) + 1` are the words `2^(2^k) + 1`,
`targetWord` is `x^195`, and `x^k` is not one for `1 ≤ k ≤ 195`, so an exponent at most 294 reaching `x^195` is 195.
-/

namespace LeanVMCircuits.Xmss

open LeanVMCircuits.Rec

theorem ofWord_eq_ev (n : ℕ) (hn : n < 2 ^ 64) : ofWord n = Rec.ev n := by
  rw [ofWord, Nat.mod_eq_of_lt hn]

/-- The word `2` is `x`. -/
theorem ofWord_two : ofWord 2 = root := by
  rw [ofWord_eq_ev 2 (by norm_num), ev_two]

/-- The digit weights' factors: the word `2^(2^k) + 1` is `x^(2^k) + 1`. -/
theorem ofWord_weight (k : ℕ) (hk : k < 3) : ofWord (2 ^ 2 ^ k + 1) = root ^ 2 ^ k + 1 := by
  have h : ∀ m : ℕ, 2 ^ m + 1 < 2 ^ 64 → 2 ^ m + 1 = 2 ^ m * 1 ^^^ 1 → ofWord (2 ^ m + 1) = root ^ m + 1 := by
    intro m hm hx
    rw [ofWord_eq_ev _ hm, hx, ev_xor, ev_two_pow_mul, ev_one, mul_one]
  interval_cases k
  · exact h 1 (by norm_num) (by decide)
  · exact h 2 (by norm_num) (by decide)
  · exact h 4 (by norm_num) (by decide)

/-- `targetWord` is `x^195`: `x^128 · x^64 · x^2 · x`. -/
theorem target_eq : ofWord Circuit.targetWord = root ^ 195 := by
  have h : Rec.mul (Rec.mul (Rec.mul (chain.getD 7 0) (chain.getD 6 0)) (chain.getD 1 0)) (chain.getD 0 0) =
      0xedb8 := by decide +kernel
  have hl : ∀ k < 64, chain.getD k 0 < 2 ^ 64 := fun k hk => (chain_squares k hk).2
  rw [Circuit.targetWord, ofWord_eq_ev _ (by norm_num), ← h, ev_mul _ _ (hl 0 (by omega)),
    ev_mul _ _ (hl 1 (by omega)), ev_mul _ _ (hl 6 (by omega)), ev_chain 7 (by omega), ev_chain 6 (by omega),
    ev_chain 1 (by omega), ev_chain 0 (by omega)]
  ring

/-- Successive products by the word `2`, each checked to be a word other than `1`. -/
def powCheck : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, a => (a != 1 && decide (a < 2 ^ 64)) && powCheck n (Rec.mul a 2)

theorem powCheck_spec : ∀ n a, powCheck n a = true → ∀ k < n,
    (fun b => Rec.mul b 2)^[k] a ≠ 1 ∧ (fun b => Rec.mul b 2)^[k] a < 2 ^ 64
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, a, h, k, hk => by
    simp only [powCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    rcases k with _ | k
    · exact ⟨h.1.1, h.1.2⟩
    · rw [Function.iterate_succ_apply]
      exact powCheck_spec n _ h.2 k (by omega)

theorem ev_iterate (k a : ℕ) : Rec.ev ((fun b => Rec.mul b 2)^[k] a) = Rec.ev a * root ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, ev_mul _ _ (by norm_num), ev_two, pow_succ']
    ring

/-- `x` has order above 195. -/
theorem root_pow_ne_one (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 195) : root ^ k ≠ 1 := by
  have hc : powCheck 195 2 = true := by decide +kernel
  obtain ⟨hne, hlt⟩ := powCheck_spec 195 2 hc (k - 1) (by omega)
  intro h
  have he : Rec.ev ((fun b => Rec.mul b 2)^[k - 1] 2) = root ^ k := by
    rw [ev_iterate, ev_two, ← pow_succ']
    rw [Nat.sub_add_cancel h1]
  apply hne
  have h' : ofWord ((fun b => Rec.mul b 2)^[k - 1] 2) = ofWord 1 := by
    rw [ofWord_eq_ev _ hlt, he, h, ofWord_eq_ev 1 (by norm_num), ev_one]
  have := congrArg toWord h'
  rwa [toWord_ofWord _ hlt, toWord_ofWord _ (by norm_num)] at this

theorem root_ne_zero : root ≠ 0 := by
  intro h
  have h' : ofWord 2 = ofWord 0 := by
    rw [ofWord_two, h, ofWord_eq_ev 0 (by norm_num), ev_zero]
  have := congrArg toWord h'
  rw [toWord_ofWord _ (by norm_num), toWord_ofWord _ (by norm_num)] at this
  exact absurd this (by norm_num)

/-- An exponent at most 294 with `x^a = x^195` is 195. -/
theorem eq_195 (a : ℕ) (ha : a ≤ 294) (h : root ^ a = root ^ 195) : a = 195 := by
  have hz : ∀ n, root ^ n ≠ 0 := fun n => pow_ne_zero n root_ne_zero
  rcases lt_trichotomy a 195 with hlt | heq | hgt
  · exfalso
    have : root ^ a * root ^ (195 - a) = root ^ a * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, h]
    exact root_pow_ne_one (195 - a) (by omega) (by omega) (mul_left_cancel₀ (hz a) this)
  · exact heq
  · exfalso
    have : root ^ 195 * root ^ (a - 195) = root ^ 195 * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hgt.le, mul_one, h]
    exact root_pow_ne_one (a - 195) (by omega) (by omega) (mul_left_cancel₀ (hz 195) this)

end LeanVMCircuits.Xmss
