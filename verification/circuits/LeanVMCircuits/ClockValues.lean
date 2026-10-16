module

public import LeanVMCircuits.Adder
public import LeanVMCircuits.BooleanOps
public import LeanVMCircuits.ClockSpec

@[expose] public section

/-!
# Word arithmetic of the clock circuit

Little-endian bit lists read as integers, slices of bit vectors, and the step's carry chain: the products
`c * x_0 * .. * x_j` of a chain of ANDs (`prefixes`), whose list read as an integer is the XOR of a word and its
successor (`carries_value`).
-/

namespace LeanVMCircuits.ClockValues

open Adder

/-- A little-endian bit list read as an integer. -/
def valueL (bits : List Bit) : ℕ := bits.foldr (fun b acc => b.val + 2 * acc) 0

theorem value_eq {n : ℕ} (bits : Vector Bit n) : value bits = valueL bits.toList := rfl

@[simp] theorem valueL_nil : valueL [] = 0 := rfl

@[simp] theorem valueL_cons (b : Bit) (bits : List Bit) : valueL (b :: bits) = b.val + 2 * valueL bits := rfl

theorem valueL_append (xs ys : List Bit) : valueL (xs ++ ys) = valueL xs + 2 ^ xs.length * valueL ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, valueL_cons, ih, List.length_cons, pow_succ]; ring

theorem valueL_take_drop (bits : List Bit) (a : ℕ) (h : a ≤ bits.length) :
    valueL bits = valueL (bits.take a) + 2 ^ a * valueL (bits.drop a) := by
  conv_lhs => rw [← List.take_append_drop a bits]
  rw [valueL_append, List.length_take, Nat.min_eq_left h]

theorem bit_val_le (b : Bit) : b.val ≤ 1 := by
  have := ZMod.val_lt b
  change b.val < 2 at this
  omega

theorem val_mul (x y : Bit) : (x * y).val = x.val * y.val := by
  rcases bit_zero_or_one x with rfl | rfl <;> rcases bit_zero_or_one y with rfl | rfl <;> decide

/-- `c + 2 Y` modulo `2^(k + 1)`, for a bit `c`. -/
theorem bit_add_two_mul_mod (c Y k : ℕ) (hc : c ≤ 1) :
    (c + 2 * Y) % 2 ^ (k + 1) = c + 2 * (Y % 2 ^ k) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdecomp := Nat.div_add_mod Y (2 ^ k)
  have hr := Nat.mod_lt Y hpos
  rw [show c + 2 * Y = (c + 2 * (Y % 2 ^ k)) + 2 ^ (k + 1) * (Y / 2 ^ k) by rw [pow_succ]; nlinarith,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]

/-- A word plus its complement is all ones. -/
theorem valueL_complement (bits : List Bit) : valueL bits + valueL (bits.map (· + 1)) + 1 = 2 ^ bits.length := by
  induction bits with
  | nil => simp
  | cons b bits ih =>
    simp only [List.map_cons, valueL_cons, List.length_cons, pow_succ]
    have : b.val + (b + 1).val = 1 := by rcases bit_zero_or_one b with rfl | rfl <;> decide
    omega

theorem value_complement {n : ℕ} (bits : Vector Bit n) :
    value bits + value (bits.map (· + 1)) + 1 = 2 ^ n := by
  rw [value_eq, value_eq, Vector.toList_map, valueL_complement, Vector.length_toList]

/-! ## Slices -/

/-- `len` consecutive entries of a vector from `start`. -/
def slice {α : Type} {n : ℕ} (v : Vector α n) (start len : ℕ) (h : start + len ≤ n) : Vector α len :=
  Vector.ofFn fun i : Fin len => v[start + i.val]

theorem toList_slice {α : Type} {n : ℕ} (v : Vector α n) (start len : ℕ) (h : start + len ≤ n) :
    (slice v start len h).toList = (v.toList.drop start).take len := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp [slice]

theorem map_slice {α β : Type} {n : ℕ} (f : α → β) (v : Vector α n) (start len : ℕ) (h : start + len ≤ n) :
    (slice v start len h).map f = slice (v.map f) start len h := by
  apply Vector.ext
  intro i hi
  simp [slice]

@[simp] theorem getElem_slice {α : Type} {n : ℕ} (v : Vector α n) (start len : ℕ) (h : start + len ≤ n)
    (i : ℕ) (hi : i < len) : (slice v start len h)[i] = v[start + i] := by
  simp [slice]

/-- A vector's value from its slices `[0, a)` and `[a, n)`. -/
theorem value_slices {n : ℕ} (v : Vector Bit n) (a b : ℕ) (h : a + b = n) :
    value v = value (slice v 0 a (by omega)) + 2 ^ a * value (slice v a b (by omega)) := by
  rw [value_eq, value_eq, value_eq, toList_slice, toList_slice, List.drop_zero,
    valueL_take_drop v.toList a (by simp; omega)]
  congr 2
  rw [List.take_of_length_le]
  simp; omega

/-- The value of a vector below its top bit, and the top bit. -/
theorem value_top {n : ℕ} (v : Vector Bit (n + 1)) :
    value v % 2 ^ n = value v.pop ∧ value v / 2 ^ n = v[n].val := by
  have h := value_pop v
  have hl : value v.pop < 2 ^ n := by simpa using value_lt v.pop
  have hb := bit_val_le v[n]
  constructor
  · rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  · rw [h, Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hl, zero_add]

theorem testBit_value_top {n : ℕ} (v : Vector Bit (n + 1)) : (value v).testBit n = decide (v[n] = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, (value_top v).2]
  rcases bit_zero_or_one v[n] with h | h <;> simp [h]

/-! ## The AND chain's carries -/

/-- The products `c * x_0 * .. * x_j` of a chain of ANDs from `c` along `xs`. -/
def prefixes (c : Bit) (xs : List Bit) : List Bit :=
  (List.range xs.length).map fun j => c * (xs.take (j + 1)).prod

@[simp] theorem length_prefixes (c : Bit) (xs : List Bit) : (prefixes c xs).length = xs.length := by
  simp [prefixes]

@[simp] theorem prefixes_nil (c : Bit) : prefixes c [] = [] := rfl

theorem prefixes_cons (c x : Bit) (xs : List Bit) : prefixes c (x :: xs) = (c * x) :: prefixes (c * x) xs := by
  simp only [prefixes, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro j _
    simp [List.take_succ_cons, mul_assoc]

theorem prefixes_append_single (c y : Bit) (xs : List Bit) :
    prefixes c (xs ++ [y]) = prefixes c xs ++ [c * (xs.prod * y)] := by
  simp only [prefixes, List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_of_length_le (by simp), List.prod_append, List.prod_singleton]

/-- Adding a bit `c` to `2 X' + b` flips bit 0 by `c` and adds the carry `b c` to `X'`. -/
theorem xor_step (X b c : ℕ) (hb : b ≤ 1) (hc : c ≤ 1) :
    (2 * X + b + c) ^^^ (2 * X + b) = c + 2 * ((X + b * c) ^^^ X) := by
  have hd : ((2 * X + b + c) ^^^ (2 * X + b)) / 2 = (X + b * c) ^^^ X := by
    rw [Nat.xor_div_two]
    congr 1 <;> interval_cases b <;> interval_cases c <;> omega
  have hm : ((2 * X + b + c) ^^^ (2 * X + b)) % 2 = c := by
    have := Nat.xor_mod_two_eq_one (a := 2 * X + b + c) (b := 2 * X + b)
    interval_cases b <;> interval_cases c <;> omega
  omega

/-- The carries of `X + c` from bit 0: the chain of ANDs from `c` along `X`'s bits reads as `(X + c) XOR X`. -/
theorem carries_value (xs : List Bit) (c : Bit) (X : ℕ) (hX : X % 2 ^ xs.length = valueL xs) :
    valueL (c :: prefixes c xs) = ((X + c.val) ^^^ X) % 2 ^ (xs.length + 1) := by
  induction xs generalizing c X with
  | nil =>
    have hb : X % 2 ≤ 1 := by omega
    have hstep := xor_step (X / 2) (X % 2) c.val hb (bit_val_le c)
    rw [show 2 * (X / 2) + X % 2 = X by omega] at hstep
    simp only [prefixes_nil, valueL_cons, valueL_nil, mul_zero, add_zero, List.length_nil, zero_add,
      pow_one]
    rw [hstep]
    have := bit_val_le c
    omega
  | cons x xs ih =>
    simp only [List.length_cons] at hX ⊢
    have hlow : X % 2 = x.val := by
      have h2 : X % 2 ^ (xs.length + 1) % 2 = X % 2 := by
        rw [pow_succ, Nat.mod_mul_left_mod]
      rw [← h2, hX, valueL_cons]
      have := bit_val_le x
      omega
    have hhigh : X / 2 % 2 ^ xs.length = valueL xs := by
      have h2 : X % 2 ^ (xs.length + 1) = X % 2 + 2 * (X / 2 % 2 ^ xs.length) := by
        rw [pow_succ', Nat.mod_mul]
      rw [hX, valueL_cons, hlow] at h2
      omega
    have hstep := xor_step (X / 2) (X % 2) c.val (by omega) (bit_val_le c)
    rw [show 2 * (X / 2) + X % 2 = X by omega] at hstep
    rw [prefixes_cons, valueL_cons, ih (c * x) (X / 2) hhigh, hstep, hlow, val_mul, mul_comm x.val c.val,
      bit_add_two_mul_mod _ _ _ (bit_val_le c)]

/-! ## The clock's ports -/

/-- The clock's bits below the live bit: its port's bits 5 to 39. -/
theorem ts_low (ts : Vector Bit 36) : (2 ^ 5 * value ts) % 2 ^ 40 = 32 * value (slice ts 0 35 (by omega)) := by
  have h := value_slices ts 35 1 rfl
  have hl := value_lt (slice ts 0 35 (by omega))
  rw [h]
  norm_num at hl ⊢
  omega

theorem ts_cycle (ts : Vector Bit 36) : value ts % 2 ^ 35 = value (slice ts 0 35 (by omega)) := by
  have h := value_slices ts 35 1 rfl
  have hl := value_lt (slice ts 0 35 (by omega))
  rw [h]
  norm_num at hl ⊢
  omega

/-- The clock's live bit, bit 40, is its port's top bit. -/
theorem ts_live (ts : Vector Bit 36) : (2 ^ 5 * value ts).testBit 40 = decide (ts[35] = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h : 2 ^ 5 * value ts / 2 ^ 40 = value ts / 2 ^ 35 := by norm_num; omega
  rw [h, (value_top ts).2]
  rcases bit_zero_or_one ts[35] with h | h <;> simp [h]

/-- A previous timestamp below its live bit: its low five bits and the 35 above them. -/
theorem prev_low (p : Vector Bit 41) :
    value p % 2 ^ 40 = value (slice p 0 5 (by omega)) + 32 * value (slice p 5 35 (by omega)) := by
  have h1 := value_slices p 40 1 rfl
  have h2 := value_slices (slice p 0 40 (by omega)) 5 35 rfl
  have e1 : slice (slice p 0 40 (by omega)) 0 5 (by omega) = slice p 0 5 (by omega) := by
    apply Vector.ext; intro i hi; simp
  have e2 : slice (slice p 0 40 (by omega)) 5 35 (by omega) = slice p 5 35 (by omega) := by
    apply Vector.ext; intro i hi; simp
  rw [e1, e2] at h2
  have hl := value_lt (slice p 0 40 (by omega))
  rw [h1, h2]
  rw [h2] at hl
  norm_num at hl ⊢
  omega

theorem zip_all_iff {α β : Type} (l1 : List α) (l2 : List β) (h : l1.length = l2.length) (f : α × β → Bool) :
    (l1.zip l2).all f = true ↔ ∀ i (h1 : i < l1.length), f (l1[i], l2[i]'(by omega)) = true := by
  simp only [List.all_eq_true, List.mem_iff_getElem, List.length_zip, List.getElem_zip]
  constructor
  · intro H i h1
    exact H _ ⟨i, by omega, rfl⟩
  · rintro H _ ⟨i, hi, rfl⟩
    exact H i (by omega)

theorem any_iff {α : Type} (l : List α) (f : α → Bool) :
    l.any f = true ↔ ∃ i, ∃ h : i < l.length, f l[i] = true := by
  simp only [List.any_eq_true, List.mem_iff_getElem]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, hf⟩
    exact ⟨i, hi, hf⟩
  · rintro ⟨i, hi, hf⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hf⟩

end LeanVMCircuits.ClockValues
