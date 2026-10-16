module

public import LeanVMCircuits.BooleanOps

@[expose] public section

/-!
# Word arithmetic of the Ext table's address incrementers

Little-endian bit lists read as integers, slices of bit vectors, the products `c * x_0 * .. * x_j` of a chain of ANDs
(`prefixes`), and the incrementer that XORs those carries into a word (`increment_value`). `incrOut` is the output of
the gate list of `increment` in `crates/leanvm_core/src/rv/semantics/ext.rs`: adding `2^b` to a word of `b + m + 2`
bits keeps its `b` low bits, flips bit `b`, and XORs into each bit above the AND of the bits from `b` below it, the
chain of `m` products over bits `b + 1 ..= b + m`, the carry out of the top bit falling off the modulus.
-/

namespace LeanVMCircuits.ExtClockValues

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

theorem valueL_lt (bits : List Bit) : valueL bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp
  | cons b bits ih =>
    have := ZMod.val_lt b
    simp only [valueL_cons, List.length_cons, pow_succ]
    change b.val < 2 at this
    omega

theorem valueL_take_drop (bits : List Bit) (a : ℕ) (h : a ≤ bits.length) :
    valueL bits = valueL (bits.take a) + 2 ^ a * valueL (bits.drop a) := by
  conv_lhs => rw [← List.take_append_drop a bits]
  rw [valueL_append, List.length_take, Nat.min_eq_left h]

theorem bit_val_le (b : Bit) : b.val ≤ 1 := by
  have := ZMod.val_lt b
  change b.val < 2 at this
  omega

theorem val_add (x y : Bit) : (x + y).val + 2 * (x * y).val = x.val + y.val := by
  rcases bit_zero_or_one x with rfl | rfl <;> rcases bit_zero_or_one y with rfl | rfl <;> decide

/-- `c + 2 Y` modulo `2^(k + 1)`, for a bit `c`. -/
theorem bit_add_two_mul_mod (c Y k : ℕ) (hc : c ≤ 1) :
    (c + 2 * Y) % 2 ^ (k + 1) = c + 2 * (Y % 2 ^ k) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdecomp := Nat.div_add_mod Y (2 ^ k)
  have hr := Nat.mod_lt Y hpos
  rw [show c + 2 * Y = (c + 2 * (Y % 2 ^ k)) + 2 ^ (k + 1) * (Y / 2 ^ k) by rw [pow_succ]; nlinarith,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]

/-- Adding `2^b` to `T + 2^b D`, `T` below `2^b`, modulo `2^(b + k)` adds one to `D` modulo `2^k`. -/
theorem shifted_mod (T D b k : ℕ) (hT : T < 2 ^ b) :
    (T + 2 ^ b * D + 2 ^ b) % 2 ^ (b + k) = T + 2 ^ b * ((D + 1) % 2 ^ k) := by
  have hd := Nat.div_add_mod (D + 1) (2 ^ k)
  have hr := Nat.mod_lt (D + 1) (Nat.two_pow_pos k)
  generalize (D + 1) / 2 ^ k = q at hd
  generalize (D + 1) % 2 ^ k = r at hd hr ⊢
  have h2 : 2 ^ b * (2 ^ k * q) + 2 ^ b * r = 2 ^ b * D + 2 ^ b := by rw [← mul_add, hd, mul_add, mul_one]
  have h3 : 2 ^ b * (r + 1) ≤ 2 ^ b * 2 ^ k := Nat.mul_le_mul_left _ hr
  rw [show T + 2 ^ b * D + 2 ^ b = (T + 2 ^ b * r) + 2 ^ (b + k) * q by rw [pow_add, mul_assoc]; linarith,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by rw [pow_add]; linarith)]

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

theorem slice_append_left {α : Type} {n k : ℕ} (x : Vector α n) (y : Vector α k) :
    slice (x ++ y) 0 n (by omega) = x := by
  apply Vector.ext
  intro i hi
  simp [Vector.getElem_append_left hi]

theorem slice_append_right {α : Type} {n k : ℕ} (x : Vector α n) (y : Vector α k) :
    slice (x ++ y) n k (by omega) = y := by
  apply Vector.ext
  intro i hi
  simp

theorem slice_slice {α : Type} {n : ℕ} (v : Vector α n) (s len t m : ℕ) (h : s + len ≤ n) (h' : t + m ≤ len) :
    slice (slice v s len h) t m h' = slice v (s + t) m (by omega) := by
  apply Vector.ext
  intro i hi
  simp [Nat.add_assoc]

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

/-! ## The incrementer -/

/-- `xs + c`, dropping the carry out: each bit XORs the carry in, which is the AND of `c` and the bits below. -/
def increment (c : Bit) : List Bit → List Bit
  | [] => []
  | x :: xs => (x + c) :: increment (c * x) xs

@[simp] theorem length_increment (c : Bit) (xs : List Bit) : (increment c xs).length = xs.length := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp [increment, ih]

theorem increment_value (c : Bit) (xs : List Bit) :
    valueL (increment c xs) = (valueL xs + c.val) % 2 ^ xs.length := by
  induction xs generalizing c with
  | nil => simp [increment]; omega
  | cons x xs ih =>
    simp only [increment, valueL_cons, ih, List.length_cons]
    have hsum := val_add x c
    rw [mul_comm c x, show x.val + 2 * valueL xs + c.val = (x + c).val + 2 * ((x * c).val + valueL xs) by
      omega, bit_add_two_mul_mod _ _ _ (bit_val_le _)]
    congr 2
    rw [Nat.add_comm]

/-- On a word with a top bit, the incrementer XORs the chain of ANDs over the bits below the top, shifted one up. -/
theorem increment_append_single (c y : Bit) (xs : List Bit) :
    increment c (xs ++ [y]) = List.zipWith (· + ·) (xs ++ [y]) (c :: prefixes c xs) := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, increment, ih, prefixes_cons, List.zipWith_cons_cons]

theorem map_zipWith_add {α β : Type} [Add α] [Add β] (f : α → β) (hf : ∀ a c, f (a + c) = f a + f c)
    (xs ys : List α) : (List.zipWith (· + ·) xs ys).map f = List.zipWith (· + ·) (xs.map f) (ys.map f) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => cases ys <;> simp [hf, ih]

/-! ## The incrementer's gate list -/

/-- The bits of `x + 2^b`, `x` of `b + m + 2` bits, from `bits`, the chain of ANDs from bit `b` over bits
`b + 1 ..= b + m`: bits below `b` unchanged, bit `b` flipped, then each bit plus the carry into it. -/
def incrOut {α : Type} [Add α] (one : α) (b m : ℕ) (x : Vector α (b + m + 2)) (bits : Vector α m) :
    Vector α (b + m + 2) :=
  (slice x 0 b (by omega) ++ (#v[x[b] + one] ++ Vector.zipWith (· + ·) (slice x (b + 1) (m + 1) (by omega))
    ((#v[x[b]] ++ bits).cast (by omega)))).cast (by omega)

theorem toList_incrOut {α : Type} [Add α] (one : α) (b m : ℕ) (x : Vector α (b + m + 2)) (bits : Vector α m) :
    (incrOut one b m x bits).toList = x.toList.take b ++ (x[b] + one) ::
      List.zipWith (· + ·) ((x.toList.drop (b + 1)).take (m + 1)) (x[b] :: bits.toList) := by
  simp [incrOut, toList_slice, Vector.toList_append, Vector.toList_cast, Vector.toList_zipWith]

theorem map_incrOut {α β : Type} [Add α] [Add β] (f : α → β) (hf : ∀ a c, f (a + c) = f a + f c) (one : α)
    (b m : ℕ) (x : Vector α (b + m + 2)) (bits : Vector α m) :
    (incrOut one b m x bits).map f = incrOut (f one) b m (x.map f) (bits.map f) := by
  apply Vector.toList_inj.mp
  rw [Vector.toList_map, toList_incrOut, toList_incrOut, List.map_append, List.map_cons, map_zipWith_add f hf,
    List.map_cons, hf, Vector.toList_map, Vector.toList_map]
  simp only [List.map_take, List.map_drop, Vector.getElem_map]

/-- The incrementer's bits as a list, `L` of `b + m + 2` bits: `L + 2^b` modulo `2^(b + m + 2)`. -/
theorem increment_list (L : List Bit) (b m : ℕ) (hlen : L.length = b + m + 2) :
    valueL (L.take b ++ (L[b]'(by omega) + 1) :: List.zipWith (· + ·) ((L.drop (b + 1)).take (m + 1))
      (L[b]'(by omega) :: prefixes (L[b]'(by omega)) ((L.drop (b + 1)).take m))) =
      (valueL L + 2 ^ b) % 2 ^ (b + m + 2) := by
  have hdrop : L.drop b = L[b]'(by omega) :: L.drop (b + 1) := List.drop_eq_getElem_cons (by omega)
  obtain ⟨R, hR⟩ : ∃ R, R = L.drop (b + 1) := ⟨_, rfl⟩
  rw [← hR] at hdrop ⊢
  have hRlen : R.length = m + 1 := by rw [hR, List.length_drop]; omega
  have hsplit : R.take m ++ [R[m]'(by omega)] = R := by
    conv_rhs => rw [← List.take_append_drop m R]
    rw [List.drop_eq_getElem_cons (show m < R.length by omega),
      List.drop_eq_nil_of_le (show R.length ≤ m + 1 by omega)]
  have key := increment_append_single (L[b]'(by omega)) (R[m]'(by omega)) (R.take m)
  rw [hsplit] at key
  have hval := increment_value 1 (L.drop b)
  rw [hdrop] at hval
  simp only [increment, one_mul, bit_one_val, List.length_cons, hRlen] at hval
  have hT : valueL (L.take b) < 2 ^ b := by
    have := valueL_lt (L.take b)
    rwa [List.length_take, Nat.min_eq_left (show b ≤ L.length by omega)] at this
  rw [List.take_of_length_le (show R.length ≤ m + 1 by omega), ← key, valueL_append, List.length_take,
    Nat.min_eq_left (show b ≤ L.length by omega), hval, ← hdrop, valueL_take_drop L b (by omega),
    show b + m + 2 = b + (m + 1 + 1) by omega, shifted_mod _ _ _ _ hT]

theorem incrOut_value (b m : ℕ) (x : Vector Bit (b + m + 2)) (bits : Vector Bit m)
    (hbits : bits.toList = prefixes x[b] (slice x (b + 1) m (by omega)).toList) :
    value (incrOut 1 b m x bits) = (value x + 2 ^ b) % 2 ^ (b + m + 2) := by
  have h := increment_list x.toList b m (by simp)
  simp only [Vector.getElem_toList] at h
  rw [value_eq, toList_incrOut, hbits, toList_slice, value_eq, h]

end LeanVMCircuits.ExtClockValues
