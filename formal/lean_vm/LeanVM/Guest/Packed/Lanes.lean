/-
  LeanVM.Guest.Packed.Lanes

  Vectors of `w`-bit lanes packed in one `ℕ`, and the whole-vector tests a certificate check runs
  as a few operations on big numbers.
-/

module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring

/-!
# Lane vectors

A vector of lanes of `w` bits is one number `v`, lane `i` at bits `[w·i, w·(i+1))`
(`lane v w i`). The kernel computes `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`,
`Nat.land`, `Nat.lor`, `Nat.xor`, the shifts, `Nat.pow` and `Nat.beq` on literals natively, so a
test of every lane at once is a few such operations, whatever the number of lanes. The tests are
written with these operations directly, and each spec states its test lane by lane:

* `fits w n v`: `v < 2^(w·n)`, its lanes from `n` on zero.
* `eqOn w lo hi a b`: lanes `lo ≤ i < hi` of `a` and `b` agree.
* `shiftEq w n a b`: lane `i + 1` of `a` is lane `i` of `b`, for `i + 1 < n`.
* `guarded w n v`: each of the first `n` lanes has its top bit clear (`< 2^(w-1)`).
* `le w n a b`: lane-wise `≤` of fitting guarded vectors, by the guard bits of `b + G - a`
  (`G = guard w n`, every lane's top bit).
* `addEq a b c`: `a + b = c`, lane-wise when no lane carries.

`nonzero w n v` is not a test but a vector: the top bit of each nonzero lane of a guarded `v`, by
the carry of `v + (2^(w-1) - 1)` into it.

`rep w n c` (`n` lanes `c`, by one division of `2^(w·n) - 1`) and `mask w lo hi` (lanes
`lo ≤ i < hi` all ones) are built from powers of two. `pack f w n`, the vector of lanes
`f 0, …, f (n-1)`, is the specs' normal form: every fitting vector is the `pack` of its lanes
(`pack_lane`), and sums and scalar products of `pack`s are `pack`s.

Reading a big vector's lanes one at a time copies it at each read: a vector to be walked is
chunked (`Chunks.lean`).
-/

namespace LeanVM.Guest.Packed

@[expose] public section

/-- Lane `i` of `v`, in lanes of `w` bits. -/
def lane (v w i : ℕ) : ℕ := Nat.mod (Nat.shiftRight v (Nat.mul w i)) (Nat.pow 2 w)

/-- The vector of lanes `f 0, …, f (n - 1)`. -/
def pack (f : ℕ → ℕ) (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => f 0 + 2 ^ w * pack (fun i ↦ f (i + 1)) w n

/-- `n` lanes of `w` bits, each `1`. -/
def ones (w n : ℕ) : ℕ := Nat.div (Nat.sub (Nat.pow 2 (Nat.mul w n)) 1) (Nat.sub (Nat.pow 2 w) 1)

/-- `n` lanes of `w` bits, each `c`. -/
def rep (w n c : ℕ) : ℕ := Nat.mul (ones w n) c

/-- Every lane's top bit, in `n` lanes of `w` bits. -/
def guard (w n : ℕ) : ℕ := rep w n (Nat.pow 2 (Nat.sub w 1))

/-- Lanes `lo ≤ i < hi` all ones, the others zero. -/
def mask (w lo hi : ℕ) : ℕ :=
  Nat.shiftLeft (Nat.sub (Nat.pow 2 (Nat.mul w (Nat.sub hi lo))) 1) (Nat.mul w lo)

/-- `v` has `n` lanes of `w` bits: `v < 2^(w·n)`. -/
def fits (w n v : ℕ) : Bool := Nat.beq (Nat.shiftRight v (Nat.mul w n)) 0

/-- Lanes `lo ≤ i < hi` of `a` and `b` agree. -/
def eqOn (w lo hi a b : ℕ) : Bool := Nat.beq (Nat.land (Nat.xor a b) (mask w lo hi)) 0

/-- Lane `i + 1` of `a` is lane `i` of `b`, for `i + 1 < n`. -/
def shiftEq (w n a b : ℕ) : Bool := eqOn w 0 (Nat.sub n 1) (Nat.shiftRight a w) b

/-- The first `n` lanes of `v` have their top bit clear. -/
def guarded (w n v : ℕ) : Bool := Nat.beq (Nat.land v (guard w n)) 0

/-- Lane-wise `a ≤ b`, for guarded vectors of `n` lanes. -/
def le (w n a b : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.sub (Nat.add b (guard w n)) a) (guard w n)) (guard w n)

/-- The top bit of each nonzero lane among the first `n` of `v`, for lanes below `2^(w-1)`: lane
`i` of `v + (2^(w-1) - 1)` reaches its top bit when lane `i` of `v` is not zero. -/
def nonzero (w n v : ℕ) : ℕ :=
  Nat.land (Nat.add v (rep w n (Nat.sub (Nat.pow 2 (Nat.sub w 1)) 1))) (guard w n)

/-- `a + b = c`: lane-wise when no lane carries. -/
def addEq (a b c : ℕ) : Bool := Nat.beq (Nat.add a b) c

end

/-! ## Lanes -/

variable {v a b c w n i lo hi : ℕ}

public theorem lane_eq (v w i : ℕ) : lane v w i = v / 2 ^ (w * i) % 2 ^ w := by
  rw [← Nat.shiftRight_eq_div_pow]; rfl

public theorem lane_lt (v w i : ℕ) : lane v w i < 2 ^ w := by
  rw [lane_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos w)

public theorem lane_zero_right (v w : ℕ) : lane v w 0 = v % 2 ^ w := by simp [lane_eq]

public theorem lane_succ (v w i : ℕ) : lane v w (i + 1) = lane (v / 2 ^ w) w i := by
  simp only [lane_eq, Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ, Nat.add_comm (w * i)]

@[simp] public theorem lane_zero_left (w i : ℕ) : lane 0 w i = 0 := by simp [lane_eq]

public theorem lane_shiftRight (v w i : ℕ) : lane (v >>> w) w i = lane v w (i + 1) := by
  rw [lane_succ, Nat.shiftRight_eq_div_pow]

public theorem testBit_lane (v w i j : ℕ) :
    (lane v w i).testBit j = (decide (j < w) && v.testBit (w * i + j)) := by
  rw [lane_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm j]

public theorem lane_land (a b w i : ℕ) : lane (a &&& b) w i = lane a w i &&& lane b w i := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [testBit_lane, Nat.testBit_land]; cases decide (j < w) <;> simp

public theorem lane_xor (a b w i : ℕ) : lane (a ^^^ b) w i = lane a w i ^^^ lane b w i := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [testBit_lane, Nat.testBit_xor]; cases decide (j < w) <;> simp

/-- `x` is zero when all its lanes are. -/
public theorem eq_zero_iff_lanes (hw : 0 < w) : v = 0 ↔ ∀ i, lane v w i = 0 := by
  refine ⟨fun h i ↦ by simp [h], fun h ↦ Nat.zero_of_testBit_eq_false fun j ↦ ?_⟩
  have := testBit_lane v w (j / w) (j % w)
  rw [h, Nat.zero_testBit, decide_eq_true (Nat.mod_lt j hw), Nat.div_add_mod] at this
  simpa using this.symm

/-- `x < 2^(k+1)` is below `2^k` when its bit `k` is clear. -/
public theorem lt_two_pow_iff_testBit {x k : ℕ} (h : x < 2 ^ (k + 1)) :
    x < 2 ^ k ↔ x.testBit k = false := by
  refine ⟨Nat.testBit_lt_two_pow, fun hk ↦ Nat.lt_pow_two_of_testBit x fun j hj ↦ ?_⟩
  rcases Nat.eq_or_lt_of_le hj with rfl | hj
  · exact hk
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hj))

/-- Bit `w·i + b` of a number, `b < w`, is in lane `i`: before lane `j` exactly when `i < j`. -/
public theorem mul_add_lt_mul {b j : ℕ} (hb : b < w) : w * i + b < w * j ↔ i < j := by
  constructor
  · intro h; by_contra hij
    exact absurd (Nat.mul_le_mul_left w (Nat.le_of_not_lt hij)) (by omega)
  · intro h
    calc w * i + b < w * i + w := by omega
      _ = w * (i + 1) := by ring
      _ ≤ w * j := Nat.mul_le_mul_left w h

/-! ## Packing -/

@[simp] public theorem pack_zero (f : ℕ → ℕ) (w : ℕ) : pack f w 0 = 0 := rfl

public theorem pack_succ (f : ℕ → ℕ) (w n : ℕ) :
    pack f w (n + 1) = f 0 + 2 ^ w * pack (fun i ↦ f (i + 1)) w n := rfl

public theorem pack_congr {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) : pack f w n = pack g w n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [pack_succ, pack_succ, h 0 (by omega), ih fun i hi ↦ h (i + 1) (by omega)]

public theorem pack_add (f g : ℕ → ℕ) (w n : ℕ) :
    pack f w n + pack g w n = pack (fun i ↦ f i + g i) w n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [pack_succ, pack_succ, pack_succ, ← ih]; ring

public theorem pack_mul (f : ℕ → ℕ) (w n c : ℕ) : pack f w n * c = pack (fun i ↦ f i * c) w n := by
  induction n generalizing f with
  | zero => simp
  | succ n ih => rw [pack_succ, pack_succ, ← ih]; ring

public theorem pack_lt {f : ℕ → ℕ} (h : ∀ i < n, f i < 2 ^ w) : pack f w n < 2 ^ (w * n) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have h0 := h 0 (by omega)
    have h1 := ih (f := fun i ↦ f (i + 1)) fun i hi ↦ h (i + 1) (by omega)
    rw [pack_succ, Nat.mul_succ, pow_add]
    calc f 0 + 2 ^ w * pack (fun i ↦ f (i + 1)) w n
        < 2 ^ w + 2 ^ w * pack (fun i ↦ f (i + 1)) w n := by omega
      _ = 2 ^ w * (pack (fun i ↦ f (i + 1)) w n + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (w * n) * 2 ^ w := by ring

public theorem lane_pack {f : ℕ → ℕ} (h : ∀ i < n, f i < 2 ^ w) (i : ℕ) :
    lane (pack f w n) w i = if i < n then f i else 0 := by
  induction n generalizing f i with
  | zero => simp
  | succ n ih =>
    have h0 := h 0 (by omega)
    rw [pack_succ]
    cases i with
    | zero => rw [lane_zero_right, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]; simp
    | succ i =>
      rw [lane_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt h0, Nat.zero_add,
        ih fun i hi ↦ h (i + 1) (by omega)]
      simp

/-- A vector of `n` lanes is the `pack` of its lanes. -/
public theorem pack_lane (h : v < 2 ^ (w * n)) : pack (lane v w) w n = v := by
  induction n generalizing v with
  | zero => simp_all
  | succ n ih =>
    have hv : v / 2 ^ w < 2 ^ (w * n) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w), ← pow_add]; rwa [Nat.mul_succ] at h
    rw [pack_succ, lane_zero_right]
    simp only [lane_succ]
    rw [ih hv, Nat.mod_add_div]

/-- Two vectors of `n` lanes are equal when their lanes are. -/
public theorem lane_ext (ha : a < 2 ^ (w * n)) (hb : b < 2 ^ (w * n)) :
    a = b ↔ ∀ i < n, lane a w i = lane b w i := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ ?_⟩
  rw [← pack_lane ha, ← pack_lane hb]; exact pack_congr h

/-! ## Constant vectors and masks -/

theorem pack_one_mul (w n : ℕ) : pack (fun _ ↦ 1) w n * (2 ^ w - 1) = 2 ^ (w * n) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pack_succ, Nat.add_mul, Nat.mul_assoc, ih, Nat.mul_succ, pow_add]
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have h2 : 2 ^ w ≤ 2 ^ w * 2 ^ (w * n) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    rw [Nat.one_mul, Nat.mul_sub, Nat.mul_one, Nat.mul_comm (2 ^ (w * n))]; omega

public theorem rep_eq (hw : 0 < w) (n c : ℕ) : rep w n c = pack (fun _ ↦ c) w n := by
  have h : 0 < 2 ^ w - 1 := by have := Nat.pow_le_pow_right (n := 2) (by omega) hw; omega
  have : ones w n = pack (fun _ ↦ 1) w n := by
    show (2 ^ (w * n) - 1) / (2 ^ w - 1) = _
    rw [← pack_one_mul, Nat.mul_div_cancel _ h]
  show ones w n * c = _
  rw [this, pack_mul]; simp

public theorem lane_rep (hw : 0 < w) (hc : c < 2 ^ w) (i : ℕ) :
    lane (rep w n c) w i = if i < n then c else 0 := by
  rw [rep_eq hw, lane_pack fun _ _ ↦ hc]

public theorem lane_guard (hw : 0 < w) (i : ℕ) :
    lane (guard w n) w i = if i < n then 2 ^ (w - 1) else 0 :=
  show lane (rep w n (2 ^ (w - 1))) w i = _ from
  lane_rep hw (Nat.pow_lt_pow_right (by omega) (by omega)) i

public theorem guard_eq (hw : 0 < w) : guard w n = pack (fun _ ↦ 2 ^ (w - 1)) w n := rep_eq hw _ _

public theorem guard_lt (hw : 0 < w) : guard w n < 2 ^ (w * n) := by
  rw [guard_eq hw]; exact pack_lt fun _ _ ↦ Nat.pow_lt_pow_right (by omega) (by omega)

public theorem lane_mask (w lo hi i : ℕ) :
    lane (mask w lo hi) w i = if lo ≤ i ∧ i < hi then 2 ^ w - 1 else 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  show (lane ((2 ^ (w * (hi - lo)) - 1) <<< (w * lo)) w i).testBit j = _
  rw [testBit_lane, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < w
  · have e1 : w * i + j ≥ w * lo ↔ lo ≤ i := by rw [ge_iff_le, ← not_lt, mul_add_lt_mul hj, not_lt]
    split_ifs with h
    · have e2 : w * i + j - w * lo = w * (i - lo) + j := by rw [Nat.mul_sub]; have := Nat.mul_le_mul_left w h.1; omega
      have e3 : w * (i - lo) + j < w * (hi - lo) := (mul_add_lt_mul hj).2 (by omega)
      simp [hj, e1.2 h.1, e2, e3]
    · rcases not_and_or.1 h with h | h
      · simp [hj, e1, h]
      · have e3 : ¬ w * i + j - w * lo < w * (hi - lo) := by
          intro e; rw [Nat.mul_sub] at e
          have := (mul_add_lt_mul hj (i := i) (j := hi)).1 (by omega); omega
        simp [e3]
  · split_ifs <;> simp [Nat.testBit_two_pow_sub_one, hj]

/-! ## The tests -/

public theorem xor_eq_zero_iff {x y : ℕ} : x ^^^ y = 0 ↔ x = y := by
  refine ⟨fun h ↦ Nat.eq_of_testBit_eq fun j ↦ ?_, fun h ↦ h ▸ Nat.xor_self x⟩
  have := congrArg (Nat.testBit · j) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  revert this; cases x.testBit j <;> cases y.testBit j <;> simp

public theorem fits_iff : fits w n v = true ↔ v < 2 ^ (w * n) := by
  show Nat.beq (v >>> (w * n)) 0 = true ↔ _
  rw [Nat.beq_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]

public theorem eqOn_iff (hw : 0 < w) :
    eqOn w lo hi a b = true ↔ ∀ i, lo ≤ i → i < hi → lane a w i = lane b w i := by
  show Nat.beq ((a ^^^ b) &&& mask w lo hi) 0 = true ↔ _
  rw [Nat.beq_eq, eq_zero_iff_lanes hw]
  refine forall_congr' fun i ↦ ?_
  rw [lane_land, lane_mask, lane_xor]
  split_ifs with h
  · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (lane_lt ..) (lane_lt ..)),
      xor_eq_zero_iff]
    exact ⟨fun e _ _ ↦ e, fun e ↦ e h.1 h.2⟩
  · simp only [Nat.and_zero, true_iff]; intro h1 h2; exact absurd ⟨h1, h2⟩ h

public theorem shiftEq_iff (hw : 0 < w) :
    shiftEq w n a b = true ↔ ∀ i, i + 1 < n → lane a w (i + 1) = lane b w i := by
  show eqOn w 0 (n - 1) (a >>> w) b = true ↔ _
  rw [eqOn_iff hw]; simp only [lane_shiftRight]
  exact ⟨fun h i hi ↦ h i (Nat.zero_le _) (by omega), fun h i _ hi ↦ h i (by omega)⟩

theorem and_top_eq_zero_iff (hw : 0 < w) (x : ℕ) (hx : x < 2 ^ w) :
    x &&& 2 ^ (w - 1) = 0 ↔ x < 2 ^ (w - 1) := by
  have hx' : x < 2 ^ (w - 1 + 1) := by rwa [Nat.sub_add_cancel hw]
  rw [lt_two_pow_iff_testBit hx', Nat.and_two_pow]
  cases x.testBit (w - 1) <;> simp

public theorem guarded_iff (hw : 0 < w) : guarded w n v = true ↔ ∀ i < n, lane v w i < 2 ^ (w - 1) := by
  show Nat.beq (v &&& guard w n) 0 = true ↔ _
  rw [Nat.beq_eq, eq_zero_iff_lanes hw]
  refine forall_congr' fun i ↦ ?_
  rw [lane_land, lane_guard hw]
  split_ifs with h
  · rw [and_top_eq_zero_iff hw _ (lane_lt ..)]; exact ⟨fun e _ ↦ e, fun e ↦ e h⟩
  · simp [h]

public theorem le_iff (hw : 0 < w) (ha : a < 2 ^ (w * n)) (hb : b < 2 ^ (w * n))
    (ga : ∀ i < n, lane a w i < 2 ^ (w - 1)) (gb : ∀ i < n, lane b w i < 2 ^ (w - 1)) :
    le w n a b = true ↔ ∀ i < n, lane a w i ≤ lane b w i := by
  show Nat.beq ((b + guard w n - a) &&& guard w n) (guard w n) = true ↔ _
  have hh : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
    rw [← Nat.two_mul, ← pow_succ', Nat.sub_add_cancel hw]
  -- `b + G - a` is the vector of the lanes `b_i + 2^(w-1) - a_i`, none borrowing.
  have he : ∀ i < n, lane b w i + 2 ^ (w - 1) - lane a w i < 2 ^ w := fun i hi ↦ by
    have := ga i hi; have := gb i hi; omega
  have hE : b + guard w n - a = pack (fun i ↦ lane b w i + 2 ^ (w - 1) - lane a w i) w n := by
    have : pack (fun i ↦ lane b w i + 2 ^ (w - 1) - lane a w i) w n + pack (lane a w) w n =
        pack (lane b w) w n + pack (fun _ ↦ 2 ^ (w - 1)) w n := by
      rw [pack_add, pack_add]
      exact pack_congr fun i hi ↦ by have := ga i hi; omega
    rw [pack_lane ha, pack_lane hb, ← guard_eq hw] at this
    omega
  rw [hE, Nat.beq_eq, lane_ext (lt_of_le_of_lt Nat.and_le_right (guard_lt hw)) (guard_lt hw)]
  refine forall₂_congr fun i hi ↦ ?_
  rw [lane_land, lane_guard hw, lane_pack he]
  simp only [hi, ↓reduceIte, Nat.and_two_pow]
  have key := lt_two_pow_iff_testBit (x := lane b w i + 2 ^ (w - 1) - lane a w i) (k := w - 1)
    (by rw [Nat.sub_add_cancel hw]; exact he i hi)
  have := ga i hi; have := gb i hi
  cases h : (lane b w i + 2 ^ (w - 1) - lane a w i).testBit (w - 1)
  · have := key.2 h
    simp only [Bool.toNat_false, Nat.zero_mul]
    constructor
    · intro h0; exact absurd h0.symm (Nat.two_pow_pos _).ne'
    · intro hle; omega
  · simp only [Bool.toNat_true, Nat.one_mul, true_iff]
    have : ¬ lane b w i + 2 ^ (w - 1) - lane a w i < 2 ^ (w - 1) := fun h' ↦ by simp [key.1 h'] at h
    omega

public theorem addEq_iff (ha : a < 2 ^ (w * n)) (hb : b < 2 ^ (w * n)) (hc : c < 2 ^ (w * n))
    (h : ∀ i < n, lane a w i + lane b w i < 2 ^ w) :
    addEq a b c = true ↔ ∀ i < n, lane a w i + lane b w i = lane c w i := by
  show Nat.beq (a + b) c = true ↔ _
  have hs : a + b = pack (fun i ↦ lane a w i + lane b w i) w n := by
    rw [← pack_add, pack_lane ha, pack_lane hb]
  rw [Nat.beq_eq, hs, lane_ext (pack_lt h) hc]
  refine forall₂_congr fun i hi ↦ ?_
  rw [lane_pack h]; simp only [hi, ↓reduceIte]

public theorem nonzero_lt (hw : 0 < w) : nonzero w n v < 2 ^ (w * n) :=
  lt_of_le_of_lt Nat.and_le_right (guard_lt hw)

public theorem nonzero_eq (hw : 0 < w) (hv : v < 2 ^ (w * n)) (gv : ∀ i < n, lane v w i < 2 ^ (w - 1)) :
    nonzero w n v = pack (fun i ↦ if lane v w i = 0 then 0 else 2 ^ (w - 1)) w n := by
  have hh : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
    rw [← Nat.two_mul, ← pow_succ', Nat.sub_add_cancel hw]
  have h1 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
  have hs : ∀ i < n, lane v w i + (2 ^ (w - 1) - 1) < 2 ^ w := fun i hi ↦ by have := gv i hi; omega
  have hlt : ∀ i < n, (if lane v w i = 0 then 0 else 2 ^ (w - 1)) < 2 ^ w := fun i _ ↦ by
    split_ifs <;> omega
  show (v + rep w n (2 ^ (w - 1) - 1)) &&& guard w n = _
  rw [rep_eq hw, ← pack_lane hv, pack_add, pack_lane hv,
    lane_ext (lt_of_le_of_lt Nat.and_le_right (guard_lt hw)) (pack_lt hlt)]
  intro i hi
  rw [lane_land, lane_pack hs, lane_guard hw, lane_pack hlt]
  simp only [hi, ↓reduceIte, Nat.and_two_pow]
  have key := lt_two_pow_iff_testBit (x := lane v w i + (2 ^ (w - 1) - 1)) (k := w - 1)
    (by rw [Nat.sub_add_cancel hw]; exact hs i hi)
  cases h : (lane v w i + (2 ^ (w - 1) - 1)).testBit (w - 1)
  · have := key.2 h; simp only [Bool.toNat_false, Nat.zero_mul]; split_ifs <;> omega
  · have : ¬ lane v w i + (2 ^ (w - 1) - 1) < 2 ^ (w - 1) := fun h' ↦ by simp [key.1 h'] at h
    simp only [Bool.toNat_true, Nat.one_mul]; split_ifs <;> omega

public theorem lane_nonzero (hw : 0 < w) (hv : v < 2 ^ (w * n))
    (gv : ∀ i < n, lane v w i < 2 ^ (w - 1)) (i : ℕ) :
    lane (nonzero w n v) w i = if i < n ∧ lane v w i ≠ 0 then 2 ^ (w - 1) else 0 := by
  have : ∀ i < n, (if lane v w i = 0 then 0 else 2 ^ (w - 1)) < 2 ^ w := fun i _ ↦ by
    split_ifs
    · exact Nat.two_pow_pos _
    · exact Nat.pow_lt_pow_right (by omega) (by omega)
  rw [nonzero_eq hw hv gv, lane_pack this]
  by_cases hi : i < n <;> by_cases h0 : lane v w i = 0 <;> simp [hi, h0]

end LeanVM.Guest.Packed
