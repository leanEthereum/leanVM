module

public import LeanVMCircuits.Multiply.Plan
public import LeanVMCircuits.Adder

@[expose] public section

/-!
The multiplier's rows as bits, and why they sum to the product.

With `e_ij = NOT (a_i XOR b_j)`, bit by bit `2 a_i b_j = a_i + b_j - 1 + e_ij`, so

```text
    2 a b = sum_ij e_ij 2^(i + j) + NOT a + NOT b + (a + b) 2^64 + 1 - 2^128
```

Column 0 there is `e_00 + NOT a_0 + NOT b_0 + 1 = 2 + 2 g` with `g = NOT a_0 NOT b_0`, so halving it, `a b` is
`1 + g` plus every other term a place lower: the 66 rows. Their positions all lie below 128.
-/

namespace LeanVMCircuits.Multiply

open BigOperators Finset

/-- A bit as an integer. -/
def iv (x : Bit) : ℤ := x.val

theorem bit_cases (x : Bit) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem iv_add (x y : Bit) : iv (x + y) = iv x + iv y - 2 * iv x * iv y := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide

theorem iv_mul (x y : Bit) : iv (x * y) = iv x * iv y := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide

theorem iv_one : iv 1 = 1 := by decide
theorem iv_zero : iv 0 = 0 := by decide

/-- A word's value from its bits. -/
def word (a : ℕ → Bit) : ℤ := ∑ i ∈ range 64, 2 ^ i * iv (a i)

/-- The complement's bit. -/
def cbit (a : ℕ → Bit) (i : ℕ) : Bit := 1 + a i

/-- `e_ij = NOT (a_i XOR b_j)`, as the multiplier builds it: `b_j XOR NOT a_i`. -/
def e (a b : ℕ → Bit) (i j : ℕ) : Bit := b j + cbit a i

/-- `g = NOT a_0 * NOT b_0`, the one product the rows cost. -/
def g (a b : ℕ → Bit) : Bit := cbit a 0 * cbit b 0

/-- Row `r`'s bit at position `p` before any step, all positions kept: `n` decides only the constant of row 64. -/
def cell (n : ℕ) (a b : ℕ → Bit) (r p : ℕ) : Bit :=
  if r < 64 then
    if r ≤ p + 1 ∧ p + 1 - r < 64 then e a b r (p + 1 - r)
    else if p = 0 ∧ r = 2 then 1 else if p = 0 ∧ r = 3 then g a b else 0
  else if r = aRow then
    if p < 63 then cbit a (p + 1) else if p < 127 then a (p - 63) else if n = 128 ∧ p = 127 then 1 else 0
  else if r = bRow then
    (if p < 63 then cbit b (p + 1) else if p < 127 then b (p - 63) else 0)
  else 0

/-- A row's value over positions below `k`. -/
def rowValue (k : ℕ) (f : ℕ → Bit) : ℤ := ∑ p ∈ range k, 2 ^ p * iv (f p)


theorem iv_e (a b : ℕ → Bit) (i j : ℕ) :
    iv (e a b i j) = 1 - iv (a i) - iv (b j) + 2 * iv (a i) * iv (b j) := by
  unfold e cbit
  rcases bit_cases (a i) with h | h <;> rcases bit_cases (b j) with h' | h' <;> rw [h, h'] <;> decide

theorem iv_cbit (a : ℕ → Bit) (i : ℕ) : iv (cbit a i) = 1 - iv (a i) := by
  unfold cbit
  rcases bit_cases (a i) with h | h <;> rw [h] <;> decide

theorem iv_g (a b : ℕ → Bit) : iv (g a b) = (1 - iv (a 0)) * (1 - iv (b 0)) := by
  rw [g, iv_mul, iv_cbit, iv_cbit]

/-- `2 a b`'s expansion over the `e_ij`. -/
theorem sum_e (a b : ℕ → Bit) :
    ∑ i ∈ range 64, ∑ j ∈ range 64, 2 ^ (i + j) * iv (e a b i j) =
      (2 ^ 64 - 1) ^ 2 - (2 ^ 64 - 1) * (word a + word b) + 2 * word a * word b := by
  have h1 : ∑ i ∈ range 64, (2 : ℤ) ^ i = 2 ^ 64 - 1 := by
    norm_num [Finset.sum_range_succ]
  simp only [iv_e, pow_add]
  have : ∀ i j : ℕ, (2 : ℤ) ^ i * 2 ^ j * (1 - iv (a i) - iv (b j) + 2 * iv (a i) * iv (b j)) =
      2 ^ i * 2 ^ j - 2 ^ i * iv (a i) * 2 ^ j - 2 ^ i * (2 ^ j * iv (b j)) +
        2 * (2 ^ i * iv (a i)) * (2 ^ j * iv (b j)) := by intro i j; ring
  simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
  rw [h1, word, word]
  ring


/-- A partial row's positions: `p = r + j - 1` for its `j`, all below 128. -/
theorem partial_row (n : ℕ) (a b : ℕ → Bit) (r : ℕ) (hr : r < 64) :
    2 * rowValue 128 (cell n a b r) = ∑ j ∈ range 64, (if 1 ≤ r + j then 2 ^ (r + j) * iv (e a b r j) else 0) +
      (if r = 2 then 2 else 0) + (if r = 3 then 2 * iv (g a b) else 0) := by
  -- The partial positions, reindexed by `j`, and the column-0 extras.
  have hsplit : rowValue 128 (cell n a b r) =
      ∑ p ∈ (range 128).filter (fun p => r ≤ p + 1 ∧ p + 1 - r < 64), 2 ^ p * iv (e a b r (p + 1 - r)) +
        ((if r = 2 then 1 else 0) + (if r = 3 then iv (g a b) else 0)) := by
    rw [rowValue, sum_filter]
    have hp : ∀ p ∈ range 128, 2 ^ p * iv (cell n a b r p) =
        (if r ≤ p + 1 ∧ p + 1 - r < 64 then 2 ^ p * iv (e a b r (p + 1 - r)) else 0) +
          (if p = 0 then (if r = 2 then 1 else 0) + (if r = 3 then iv (g a b) else 0) else 0) := by
      intro p _
      simp only [cell, if_pos hr]
      by_cases hc : r ≤ p + 1 ∧ p + 1 - r < 64
      · have : ¬ (p = 0 ∧ (r = 2 ∨ r = 3)) := by omega
        rw [if_pos hc, if_pos hc]
        by_cases h0 : p = 0
        · have h2 : r ≠ 2 := by omega
          have h3 : r ≠ 3 := by omega
          simp [h0, h2, h3]
        · simp [h0]
      · rw [if_neg hc, if_neg hc, zero_add]
        by_cases h0 : p = 0
        · subst h0
          by_cases h2 : r = 2
          · simp [h2, iv_one]
          · by_cases h3 : r = 3
            · simp [h3]
            · simp [h2, h3, iv_zero]
        · simp [h0, iv_zero]
    rw [sum_congr rfl hp, sum_add_distrib, sum_ite_eq' (range 128) 0]
    simp
  have hbij : ∑ p ∈ (range 128).filter (fun p => r ≤ p + 1 ∧ p + 1 - r < 64), 2 ^ p * iv (e a b r (p + 1 - r)) =
      ∑ j ∈ (range 64).filter (fun j => 1 ≤ r + j), 2 ^ (r + j - 1) * iv (e a b r j) := by
    apply sum_nbij' (fun p => p + 1 - r) (fun j => r + j - 1)
    · intro p hp; simp only [mem_filter, mem_range] at hp ⊢; omega
    · intro j hj; simp only [mem_filter, mem_range] at hj ⊢; omega
    · intro p hp; simp only [mem_filter, mem_range] at hp; omega
    · intro j hj; simp only [mem_filter, mem_range] at hj; omega
    · intro p hp
      simp only [mem_filter, mem_range] at hp
      rw [show r + (p + 1 - r) - 1 = p by omega]
  have hA : 2 * ∑ j ∈ (range 64).filter (fun j => 1 ≤ r + j), 2 ^ (r + j - 1) * iv (e a b r j) =
      ∑ j ∈ range 64, (if 1 ≤ r + j then 2 ^ (r + j) * iv (e a b r j) else 0) := by
    rw [mul_sum, sum_filter]
    apply sum_congr rfl
    intro j _
    split_ifs with h
    · rw [← mul_assoc, ← pow_succ', show r + j - 1 + 1 = r + j by omega]
    · rfl
  have hB : (2 : ℤ) * ((if r = 2 then 1 else 0) + (if r = 3 then iv (g a b) else 0)) =
      (if r = 2 then 2 else 0) + (if r = 3 then 2 * iv (g a b) else 0) := by
    split_ifs <;> ring
  rw [hsplit, hbij, mul_add, hA, hB, add_assoc]


/-- The `a` row and the `b` row: the complement's upper bits, then the word, and for 128 bits half of `2^128`. -/
theorem side_row (n : ℕ) (a b : ℕ → Bit) (r : ℕ) (hr : r = aRow ∨ r = bRow) :
    rowValue 128 (cell n a b r) =
      ∑ p ∈ range 63, 2 ^ p * iv (cbit (if r = aRow then a else b) (p + 1)) +
        2 ^ 63 * word (if r = aRow then a else b) + (if r = aRow ∧ n = 128 then 2 ^ 127 else 0) := by
  have hn : ¬ r < 64 := by rcases hr with rfl | rfl <;> decide
  rw [rowValue, show (128 : ℕ) = 127 + 1 from rfl, sum_range_succ, show (127 : ℕ) = 63 + 64 from rfl, sum_range_add]
  have h1 : ∀ p ∈ range 63, 2 ^ p * iv (cell n a b r p) =
      2 ^ p * iv (cbit (if r = aRow then a else b) (p + 1)) := by
    intro p hp
    simp only [mem_range] at hp
    rcases hr with rfl | rfl <;> simp [cell, aRow, bRow, hp]
  have h2 : ∀ k ∈ range 64, 2 ^ (63 + k) * iv (cell n a b r (63 + k)) =
      2 ^ 63 * (2 ^ k * iv ((if r = aRow then a else b) k)) := by
    intro k hk
    simp only [mem_range] at hk
    rw [← mul_assoc, ← pow_add]
    rcases hr with rfl | rfl <;> simp [cell, aRow, bRow, show 63 + k < 127 by omega]
  rw [sum_congr rfl h1, sum_congr rfl h2, ← mul_sum, word]
  congr 1
  rcases hr with rfl | rfl
  · by_cases h : n = 128 <;> simp [cell, aRow, h, iv_one, iv_zero]
  · simp [cell, aRow, bRow, iv_zero]


/-- The rows before any step sum to the product, plus `2^127` once or twice: zero modulo `2^64`, and modulo `2^128`
when the 128-bit rows carry the second. -/
theorem rows_sum (n : ℕ) (a b : ℕ → Bit) :
    ∑ r ∈ range nRows, rowValue 128 (cell n a b r) =
      word a * word b + 2 ^ 127 + (if n = 128 then 2 ^ 127 else 0) := by
  rw [show nRows = 64 + 1 + 1 from rfl, sum_range_succ, sum_range_succ]
  have hP : 2 * ∑ r ∈ range 64, rowValue 128 (cell n a b r) =
      ∑ r ∈ range 64, ∑ j ∈ range 64, 2 ^ (r + j) * iv (e a b r j) - iv (e a b 0 0) + 2 + 2 * iv (g a b) := by
    rw [mul_sum, sum_congr rfl fun r hr => partial_row n a b r (mem_range.mp hr)]
    rw [sum_add_distrib, sum_add_distrib, sum_ite_eq' (range 64) 2, sum_ite_eq' (range 64) 3]
    simp only [mem_range, show (2 : ℕ) < 64 by omega, show (3 : ℕ) < 64 by omega, if_true]
    have hz : ∑ r ∈ range 64, ∑ j ∈ range 64, (if 1 ≤ r + j then 2 ^ (r + j) * iv (e a b r j) else 0) =
        ∑ r ∈ range 64, ∑ j ∈ range 64, 2 ^ (r + j) * iv (e a b r j) - iv (e a b 0 0) := by
      have hf : ∀ r j : ℕ, (if 1 ≤ r + j then (2 : ℤ) ^ (r + j) * iv (e a b r j) else 0) =
          2 ^ (r + j) * iv (e a b r j) - (if r = 0 then (if j = 0 then 2 ^ (r + j) * iv (e a b r j) else 0) else 0) := by
        intro r j
        by_cases hr : r = 0 <;> by_cases hj : j = 0 <;> simp [hr, hj]
      have h00 : ∑ r ∈ range 64, ∑ j ∈ range 64,
          (if r = 0 then (if j = 0 then (2 : ℤ) ^ (r + j) * iv (e a b r j) else 0) else 0) = iv (e a b 0 0) := by
        rw [sum_eq_single 0 (fun r _ hr => by simp [hr]) (by simp)]
        rw [sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp)]
        simp
      simp only [hf, sum_sub_distrib, h00]
    rw [hz]
    try ring
  have hA := side_row n a b aRow (Or.inl rfl)
  have hB := side_row n a b bRow (Or.inr rfl)
  simp only [show aRow = 64 from rfl, show bRow = 65 from rfl, if_true, show (65 : ℕ) ≠ 64 by omega, if_false,
    true_and, false_and] at hA hB
  have hC : ∀ c : ℕ → Bit, 2 * ∑ p ∈ range 63, 2 ^ p * iv (cbit c (p + 1)) =
      (2 ^ 64 - 1 - word c) - (1 - iv (c 0)) := by
    intro c
    have h64 : ∑ i ∈ range 64, 2 ^ i * iv (cbit c i) = 2 ^ 64 - 1 - word c := by
      simp only [iv_cbit, mul_sub, mul_one, sum_sub_distrib, word]
      norm_num [Finset.sum_range_succ]
    have hs : ∑ i ∈ range 64, (2 : ℤ) ^ i * iv (cbit c i) =
        ∑ p ∈ range 63, 2 ^ (p + 1) * iv (cbit c (p + 1)) + 2 ^ 0 * iv (cbit c 0) :=
      sum_range_succ' (fun i => (2 : ℤ) ^ i * iv (cbit c i)) 63
    rw [← h64, hs, mul_sum, iv_cbit]
    have : ∀ p ∈ range 63, (2 : ℤ) * (2 ^ p * iv (cbit c (p + 1))) = 2 ^ (p + 1) * iv (cbit c (p + 1)) := by
      intro p _; ring
    rw [sum_congr rfl this]
    ring
  have hsum := sum_e a b
  have he := iv_e a b 0 0
  have hg := iv_g a b
  have hcA := hC a
  have hcB := hC b
  rw [show (64 : ℕ) + 1 = 65 from rfl] at *
  have key : 2 * (∑ r ∈ range 64, rowValue 128 (cell n a b r) + rowValue 128 (cell n a b 64) +
      rowValue 128 (cell n a b 65)) = 2 * (word a * word b + 2 ^ 127 + (if n = 128 then 2 ^ 127 else 0)) := by
    rw [mul_add, mul_add, hP, hA, hB]
    split_ifs <;> nlinarith [hsum, he, hg, hcA, hcB]
  linarith

end LeanVMCircuits.Multiply
