/-
  LeanVM.Guest.B1.Sig.XmssGroups

  leanXMSS's codeword digits, dispatched four at a time (`verify_lean_xmss`, `walk_group`,
  `lean_ethereum.py:3565-3579, 3682-3702`): fourteen groups of four and a group of the last two,
  their digit sums and their encoding.
-/

module

public import LeanVM.Guest.B1.Sig.Codeword

/-!
# The codeword's groups of four

A layer's `58` digits are hinted as `LX_DIGIT_DISPATCHES = 15` groups in the exponent
(`lx_digits`), group `p` the digits `4p, …` (`LX_GROUP_SIZES`: `4`, the last `2`), dispatched over
`4^4` arms each, the last one's table as wide, its range check keeping it below `4^2`. Arm `k` of
group `p` walks chain `4p + r` at digit `k / 4^r % 4`, folds `DIGIT_SUMS[k % 4^n]` into the
product, in the exponent, and `(k % 4^n) · 4^(4p)` into the encoding.

* `lxN p`: group `p`'s digits; `lxDigit K i`: chain `i`'s digit when group `p` takes arm `K p`;
* `digitSum_mod`: `DIGIT_SUMS` over `4^4` entries is the digit sum of a group's own digits;
* `lx_digitSum_total`: the groups' digit sums add up to the digits' sum;
* `lx_enc_total`, `lx_enc_lt`, `lx_enc_step`: the groups' encodings add up, without carries, to the
  digits' base-4 number, a `lit` of each running sum.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Value

@[expose] public section

/-- Group `p`'s digits (`LX_GROUP_SIZES`): four, the last group two. -/
def lxN (p : Nat) : Nat := if p < 14 then 4 else 2

/-- Chain `i`'s digit when each group `p` takes arm `K p`. -/
def lxDigit (K : Nat → Nat) (i : Nat) : Nat := K (i / 4) / 4 ^ (i % 4) % 4

theorem lxDigit_lt (K : Nat → Nat) (i : Nat) : lxDigit K i < 4 := Nat.mod_lt _ (by norm_num)

theorem digitSum_four (k : Nat) : digitSum k 4 = k % 4 + k / 4 % 4 + k / 16 % 4 + k / 64 % 4 := by
  simp [digitSum]; omega

theorem digitSum_two (k : Nat) : digitSum k 2 = k % 4 + k / 4 % 4 := by
  simp [digitSum]; omega

/-- **`DIGIT_SUMS[k % 4^n]`**, the table's sum of four digits, is the sum of `k`'s low `n`. -/
theorem digitSum_mod (k : Nat) {n : Nat} (hn : n = 2 ∨ n = 4) : digitSum (k % 4 ^ n) 4 = digitSum k n := by
  rcases hn with rfl | rfl
  · rw [digitSum_four, digitSum_two]; norm_num; omega
  · rw [digitSum_four, digitSum_four]; norm_num; omega

theorem lx_digitSum_le (k n : Nat) : digitSum k n ≤ 3 * n := by
  induction n with
  | zero => simp [digitSum]
  | succ n ih =>
      simp only [digitSum]
      have : k / 4 ^ n % 4 < 4 := Nat.mod_lt _ (by norm_num)
      omega

/-- A sum over the `58` chains, by groups. -/
theorem sum_range_58 {M : Type} [AddCommMonoid M] (g : Nat → M) :
    ∑ i ∈ Finset.range 58, g i = ∑ p ∈ Finset.range 14,
      (g (4 * p) + g (4 * p + 1) + g (4 * p + 2) + g (4 * p + 3)) + (g 56 + g 57) := by
  have h : ∀ m, ∑ i ∈ Finset.range (4 * m), g i =
      ∑ p ∈ Finset.range m, (g (4 * p) + g (4 * p + 1) + g (4 * p + 2) + g (4 * p + 3)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ (n := m), ← ih, show 4 * (m + 1) = 4 * m + 3 + 1 by ring,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [add_assoc]
  rw [show (58 : Nat) = 4 * 14 + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ, h,
    add_assoc]

/-- **The groups' digit sums add up to the digits' sum.** -/
theorem lx_digitSum_total (K : Nat → Nat) :
    ∑ p ∈ Finset.range 15, digitSum (K p) (lxN p) = ∑ i ∈ Finset.range 58, lxDigit K i := by
  rw [sum_range_58, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    have hp' : p < 14 := Finset.mem_range.mp hp
    simp only [lxN, hp', ↓reduceIte, digitSum_four, lxDigit,
      show (4 * p) / 4 = p by omega, show (4 * p + 1) / 4 = p by omega,
      show (4 * p + 2) / 4 = p by omega, show (4 * p + 3) / 4 = p by omega,
      show (4 * p) % 4 = 0 by omega, show (4 * p + 1) % 4 = 1 by omega,
      show (4 * p + 2) % 4 = 2 by omega, show (4 * p + 3) % 4 = 3 by omega]
    norm_num
  · simp only [lxN, show ¬ (14 < 14) by omega, ↓reduceIte, digitSum_two, lxDigit]
    norm_num

/-- Group `p`'s term of the encoding. -/
def lxEncTerm (K : Nat → Nat) (p : Nat) : Nat := K p % 4 ^ lxN p * 4 ^ (4 * p)

theorem group_enc4 (k X : Nat) : k % 4 ^ 4 * X = k / 4 ^ 0 % 4 * 4 ^ 0 * X + k / 4 ^ 1 % 4 * 4 ^ 1 * X +
    k / 4 ^ 2 % 4 * 4 ^ 2 * X + k / 4 ^ 3 % 4 * 4 ^ 3 * X := by
  have e : k % 4 ^ 4 = k / 4 ^ 0 % 4 * 4 ^ 0 + k / 4 ^ 1 % 4 * 4 ^ 1 + k / 4 ^ 2 % 4 * 4 ^ 2 +
      k / 4 ^ 3 % 4 * 4 ^ 3 := by norm_num; omega
  rw [e]; ring

theorem group_enc2 (k X : Nat) : k % 4 ^ 2 * X = k / 4 ^ 0 % 4 * 4 ^ 0 * X + k / 4 ^ 1 % 4 * 4 ^ 1 * X := by
  have e : k % 4 ^ 2 = k / 4 ^ 0 % 4 * 4 ^ 0 + k / 4 ^ 1 % 4 * 4 ^ 1 := by norm_num; omega
  rw [e]; ring

/-- **The groups' encodings add up to the digits' base-4 number.** -/
theorem lx_enc_total (K : Nat → Nat) :
    ∑ p ∈ Finset.range 15, lxEncTerm K p = ∑ i ∈ Finset.range 58, lxDigit K i * 4 ^ i := by
  rw [sum_range_58, Finset.sum_range_succ]
  have hd : ∀ p r, r < 4 → lxDigit K (4 * p + r) * 4 ^ (4 * p + r) = K p / 4 ^ r % 4 * 4 ^ r * 4 ^ (4 * p) := by
    intro p r hr
    simp only [lxDigit, show (4 * p + r) / 4 = p by omega, show (4 * p + r) % 4 = r by omega, pow_add]
    ring
  refine congrArg₂ (· + ·) ?_ ?_
  · apply Finset.sum_congr rfl
    intro p hp
    have hp' : p < 14 := Finset.mem_range.mp hp
    rw [show 4 * p = 4 * p + 0 from rfl, hd p 0 (by omega), hd p 1 (by omega), hd p 2 (by omega),
      hd p 3 (by omega)]
    simp only [lxEncTerm, lxN, hp', ↓reduceIte]
    exact group_enc4 _ _
  · rw [show (56 : Nat) = 4 * 14 + 0 from rfl, show (57 : Nat) = 4 * 14 + 1 from rfl, hd 14 0 (by omega),
      hd 14 1 (by omega)]
    simp only [lxEncTerm, lxN, show ¬ (14 < 14) by omega, ↓reduceIte]
    exact group_enc2 _ _

theorem lxEncTerm_lt (K : Nat → Nat) (p : Nat) : lxEncTerm K p < 2 ^ 8 * 2 ^ (8 * p) := by
  unfold lxEncTerm
  have h1 : K p % 4 ^ lxN p < 2 ^ 8 := by
    have := Nat.mod_lt (K p) (show 0 < 4 ^ lxN p by positivity)
    have : 4 ^ lxN p ≤ 2 ^ 8 := by unfold lxN; split <;> norm_num
    omega
  rw [show (4 : Nat) ^ (4 * p) = 2 ^ (8 * p) by rw [pow_mul, pow_mul]; norm_num]
  exact Nat.mul_lt_mul_of_pos_right h1 (by positivity)

/-- The running encodings are below `2^(8p)`. -/
theorem lx_enc_lt (K : Nat → Nat) : ∀ p, ∑ q ∈ Finset.range p, lxEncTerm K q < 2 ^ (8 * p)
  | 0 => by simp
  | p + 1 => by
      rw [Finset.sum_range_succ]
      have ih := lx_enc_lt K p
      have h := lxEncTerm_lt K p
      have h' : lxEncTerm K p + 2 ^ (8 * p) ≤ 2 ^ 8 * 2 ^ (8 * p) := by
        have : lxEncTerm K p ≤ 2 ^ 8 * 2 ^ (8 * p) - 2 ^ (8 * p) := by
          have hd : lxEncTerm K p * 1 < 2 ^ 8 * 2 ^ (8 * p) := by simpa using h
          have : 2 ^ (8 * p) ∣ lxEncTerm K p := by
            unfold lxEncTerm
            exact Dvd.dvd.mul_left (by rw [show (4 : Nat) ^ (4 * p) = 2 ^ (8 * p) by
              rw [pow_mul, pow_mul]; norm_num]) _
          obtain ⟨c, hc⟩ := this
          rw [hc] at h ⊢
          have hc' : c < 2 ^ 8 := by
            rw [mul_comm] at h
            exact Nat.lt_of_mul_lt_mul_right h
          have : 2 ^ (8 * p) * c ≤ 2 ^ (8 * p) * (2 ^ 8 - 1) := Nat.mul_le_mul_left _ (by omega)
          rw [Nat.mul_sub, mul_one] at this
          rw [mul_comm (2 ^ 8)]
          exact this
        have : 2 ^ (8 * p) ≤ 2 ^ 8 * 2 ^ (8 * p) := Nat.le_mul_of_pos_left _ (by norm_num)
        omega
      rw [show 8 * (p + 1) = 8 + 8 * p by ring, pow_add]
      omega

/-- **One group folded into the encoding**: the `lit` of the running sum plus the group's
`lit`. -/
theorem lx_enc_step (K : Nat → Nat) {p : Nat} (hp : p < 15) :
    lit (∑ q ∈ Finset.range p, lxEncTerm K q) + lit (lxEncTerm K p) =
      lit (∑ q ∈ Finset.range (p + 1), lxEncTerm K q) := by
  have h120 : ∀ q ≤ 15, 2 ^ (8 * q) ≤ 2 ^ 120 := fun q hq =>
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs := lx_enc_lt K p
  have hs1 := lx_enc_lt K (p + 1)
  have ht : lxEncTerm K p < 2 ^ 128 :=
    lt_of_lt_of_le (lxEncTerm_lt K p) (by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have hd : 2 ^ (8 * p) ∣ lxEncTerm K p := by
    unfold lxEncTerm
    exact Dvd.dvd.mul_left (by rw [show (4 : Nat) ^ (4 * p) = 2 ^ (8 * p) by
      rw [pow_mul, pow_mul]; norm_num]) _
  obtain ⟨c, hc⟩ := hd
  rw [lit_eq _ (by have := h120 p (by omega); omega), lit_eq _ ht,
    lit_eq _ (by have := h120 (p + 1) (by omega); omega), Finset.sum_range_succ, hc,
    eOfNat128_add_shift hs]

end
end LeanVM.Guest.B1.Sig
