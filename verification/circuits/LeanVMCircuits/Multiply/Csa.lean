module

public import LeanVMCircuits.Multiply.Value

@[expose] public section

/-!
One carry-save step and the final ripple addition, on bits.

A step's sum row is the XOR of its three rows, and its carry row holds each product position's majority one place up
and each moved bit in place. Where the plan puts a product, a full adder; where it moves a bit, the two bits present
already sum without carry; elsewhere at most one bit is present, or the position is the top one, whose carry leaves
the modulus. So the two rows' values sum to the three's, modulo `2^n`. The ripple addition is the same with the carry
chained along the positions.
-/

namespace LeanVMCircuits.Multiply

open BigOperators Finset

/-- A row is zero wherever its mask has no bit. -/
def ZeroOff (f : ℕ → Bit) (m : ℕ) : Prop := ∀ p, bit m p = false → f p = 0

/-- The majority of three bits, as the step computes it from its product. -/
def maj (x y z : Bit) : Bit := (x + z) * (y + z) + z

theorem full_adder (x y z : Bit) : iv x + iv y + iv z = iv (x + y + z) + 2 * iv (maj x y z) := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;>
    rcases bit_cases z with rfl | rfl <;> decide

/-- The step's rows from rows `x`, `y`, `z`. -/
def sumRow (s : Csa) (x y z : ℕ → Bit) (p : ℕ) : Bit :=
  if bit s.moveZ p then x p + y p else if bit s.moveY p then x p else x p + y p + z p

def carryRow (s : Csa) (x y z : ℕ → Bit) (q : ℕ) : Bit :=
  if 0 < q ∧ bit s.products (q - 1) then maj (x (q - 1)) (y (q - 1)) (z (q - 1))
  else if bit s.moveZ q then z q else if bit s.moveY q then y q else 0

/-- What a step's masks must satisfy: the plan's conditions, decided for every step of the two plans. -/
structure StepOK (n : ℕ) (s : Csa) (px py pz : ℕ) : Prop where
  /-- Every position with two bits or more below the top takes a product or a move. -/
  covered : ∀ p, p + 1 < n → 2 ≤ (if bit px p then 1 else 0) + (if bit py p then 1 else 0) +
    (if bit pz p then 1 else 0) → bit s.products p ∨ bit s.moveY p ∨ bit s.moveZ p
  /-- Products lie below the top. -/
  productsLow : ∀ p, bit s.products p → p + 1 < n
  /-- A moved `z` has exactly one of `x` and `y` beside it. -/
  moveZ : ∀ p, bit s.moveZ p → bit pz p ∧ (bit px p != bit py p) ∧ ¬ bit s.products p
  /-- A moved `y` has `x` beside it and no `z`. -/
  moveY : ∀ p, bit s.moveY p → bit px p ∧ bit py p ∧ ¬ bit pz p ∧ ¬ bit s.moveZ p ∧ ¬ bit s.products p
  /-- The carry row is free where a bit moves into it. -/
  free : ∀ q, 0 < q → bit s.products (q - 1) → ¬ bit s.moveZ q ∧ ¬ bit s.moveY q


theorem iv_add_of_zero (x y : Bit) (h : x = 0 ∨ y = 0) : iv (x + y) = iv x + iv y := by
  rcases h with rfl | rfl <;> simp [iv_zero]

theorem iv_le_one (x : Bit) : iv x ≤ 1 := by rcases bit_cases x with rfl | rfl <;> decide
theorem iv_nonneg (x : Bit) : 0 ≤ iv x := by rcases bit_cases x with rfl | rfl <;> decide

/-- The carry row's contribution at position `q` before reindexing. -/
def carryPart (s : Csa) (x y z : ℕ → Bit) (p : ℕ) : ℤ :=
  (if bit s.products p then 2 ^ (p + 1) * iv (maj (x p) (y p) (z p)) else 0) +
    (if bit s.moveZ p then 2 ^ p * iv (z p) else 0) + (if bit s.moveY p then 2 ^ p * iv (y p) else 0)

/-- At each position the three bits are the sum bit, the carry contributions, and at the top a multiple of `2^n`. -/
theorem position (n : ℕ) (s : Csa) (px py pz : ℕ) (hok : StepOK n s px py pz) (x y z : ℕ → Bit)
    (hx : ZeroOff x px) (hy : ZeroOff y py) (hz : ZeroOff z pz) (p : ℕ) (hp : p < n) :
    ∃ k : ℤ, 2 ^ p * (iv (x p) + iv (y p) + iv (z p)) =
      2 ^ p * iv (sumRow s x y z p) + carryPart s x y z p + 2 ^ n * k := by
  by_cases hprod : bit s.products p
  · have hz' : ¬ bit s.moveZ p := fun h => (hok.moveZ p h).2.2 hprod
    have hy' : ¬ bit s.moveY p := fun h => (hok.moveY p h).2.2.2.2 hprod
    refine ⟨0, ?_⟩
    simp only [sumRow, carryPart, hprod, hz', hy', if_true, if_false, Bool.false_eq_true]
    rw [full_adder, pow_succ]
    ring
  · by_cases hmz : bit s.moveZ p
    · obtain ⟨_, hne, _⟩ := hok.moveZ p hmz
      have hxy : x p = 0 ∨ y p = 0 := by
        cases hbx : bit px p
        · exact Or.inl (hx p hbx)
        · rw [hbx] at hne; cases hby : bit py p
          · exact Or.inr (hy p hby)
          · rw [hby] at hne; simp at hne
      have hmy : ¬ bit s.moveY p := fun h => (hok.moveY p h).2.2.2.1 hmz
      refine ⟨0, ?_⟩
      simp only [sumRow, carryPart, hprod, hmz, hmy, if_true, if_false, Bool.false_eq_true]
      rw [iv_add_of_zero _ _ hxy]
      ring
    · by_cases hmy : bit s.moveY p
      · obtain ⟨_, _, hzp, _, _⟩ := hok.moveY p hmy
        have hz0 : z p = 0 := hz p (by simpa using hzp)
        refine ⟨0, ?_⟩
        simp only [sumRow, carryPart, hprod, hmz, hmy, if_true, if_false, Bool.false_eq_true, hz0, iv_zero]
        ring
      · simp only [sumRow, carryPart, hprod, hmz, hmy, if_false, Bool.false_eq_true, add_zero]
        by_cases htop : p + 1 < n
        · -- Below the top, at most one bit is present.
          have hcount : ¬ 2 ≤ (if bit px p then 1 else 0) + (if bit py p then 1 else 0) +
              (if bit pz p then 1 else 0) := fun h => by
            rcases hok.covered p htop h with h | h | h <;> simp_all
          refine ⟨0, ?_⟩
          have hxv := hx p; have hyv := hy p; have hzv := hz p
          cases bx : bit px p <;> cases by' : bit py p <;> cases bz : bit pz p <;>
            simp_all [iv_zero]
        · -- At the top, the carry leaves the modulus.
          have hpn : p + 1 = n := by omega
          refine ⟨iv (maj (x p) (y p) (z p)), ?_⟩
          rw [full_adder, ← hpn, pow_succ]
          ring


/-- The carry row's value is the sum of the positions' carry contributions. -/
theorem carry_value (n : ℕ) (s : Csa) (px py pz : ℕ) (hok : StepOK n s px py pz) (x y z : ℕ → Bit) :
    rowValue n (carryRow s x y z) = ∑ p ∈ range n, carryPart s x y z p := by
  -- Split each contribution into its product part and its moved part.
  have hsplit : ∀ q, 2 ^ q * iv (carryRow s x y z q) =
      (if 0 < q ∧ bit s.products (q - 1) then 2 ^ q * iv (maj (x (q - 1)) (y (q - 1)) (z (q - 1))) else 0) +
        ((if bit s.moveZ q then 2 ^ q * iv (z q) else 0) + (if bit s.moveY q then 2 ^ q * iv (y q) else 0)) := by
    intro q
    unfold carryRow
    by_cases hp : 0 < q ∧ bit s.products (q - 1)
    · obtain ⟨h1, h2⟩ := hok.free q hp.1 hp.2
      simp [hp, h1, h2]
    · by_cases hz : bit s.moveZ q
      · have : ¬ bit s.moveY q := fun h => (hok.moveY q h).2.2.2.1 hz
        simp [hp, hz, this]
      · simp only [hp, hz, if_false, Bool.false_eq_true, zero_add]
        split_ifs <;> simp [iv_zero]
  -- The product parts: position `q = p + 1` takes position `p`'s majority, and products lie below the top.
  have hprod : ∑ q ∈ range n, (if 0 < q ∧ bit s.products (q - 1) then
      (2 : ℤ) ^ q * iv (maj (x (q - 1)) (y (q - 1)) (z (q - 1))) else 0) =
      ∑ p ∈ range n, (if bit s.products p then 2 ^ (p + 1) * iv (maj (x p) (y p) (z p)) else 0) := by
    cases n with
    | zero => simp
    | succ m =>
      rw [sum_range_succ' _ m, sum_range_succ _ m]
      have htop : ¬ bit s.products m := fun h => by have := hok.productsLow m h; omega
      simp only [htop, if_false, add_zero, lt_irrefl, false_and, Bool.false_eq_true]
      apply sum_congr rfl
      intro p _
      simp only [Nat.succ_pos, true_and, Nat.add_sub_cancel]
  rw [rowValue, sum_congr rfl fun q _ => hsplit q]
  unfold carryPart
  simp only [sum_add_distrib]
  rw [hprod]
  ring

theorem zeroOff_iv (f : ℕ → Bit) (m : ℕ) (hf : ZeroOff f m) (n : ℕ) (hm : m < 2 ^ n) (p : ℕ) (hp : n ≤ p) :
    f p = 0 := hf p (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hp)))

/-- A step keeps the rows' total modulo `2^n`. -/
theorem step_value (n : ℕ) (s : Csa) (px py pz : ℕ) (hok : StepOK n s px py pz) (x y z : ℕ → Bit)
    (hx : ZeroOff x px) (hy : ZeroOff y py) (hz : ZeroOff z pz) :
    ∃ k : ℤ, rowValue n x + rowValue n y + rowValue n z =
      rowValue n (sumRow s x y z) + rowValue n (carryRow s x y z) + 2 ^ n * k := by
  choose k hk using fun (p : Fin n) => position n s px py pz hok x y z hx hy hz p.val p.isLt
  refine ⟨∑ p : Fin n, k p, ?_⟩
  rw [carry_value n s px py pz hok, rowValue, rowValue, rowValue, rowValue, ← sum_add_distrib, ← sum_add_distrib,
    ← sum_add_distrib, mul_sum, ← Fin.sum_univ_eq_sum_range (fun p => 2 ^ p * iv (x p) + 2 ^ p * iv (y p) +
      2 ^ p * iv (z p)), ← Fin.sum_univ_eq_sum_range, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [← hk p]
  ring


/-! The ripple addition of the last two rows. -/

/-- The carry into each position: the majority out of the position below where it takes a product. -/
def cin (cm : ℕ) (x y : ℕ → Bit) : ℕ → Bit
  | 0 => 0
  | p + 1 => if bit cm p then maj (x p) (y p) (cin cm x y p) else 0

/-- The sum's bits. -/
def ripple (cm : ℕ) (x y : ℕ → Bit) (p : ℕ) : Bit := x p + y p + cin cm x y p

/-- The plan's carries: every position below the top with two bits or more, counting the carry in, takes one. -/
structure RippleOK (n cm px py : ℕ) : Prop where
  covered : ∀ p, p + 1 < n → 2 ≤ (if bit px p then 1 else 0) + (if bit py p then 1 else 0) +
    (if 0 < p ∧ bit cm (p - 1) then 1 else 0) → bit cm p
  low : ∀ p, bit cm p → p + 1 < n

theorem cin_zero (cm : ℕ) (x y : ℕ → Bit) (p : ℕ) (h : ¬ (0 < p ∧ bit cm (p - 1))) : cin cm x y p = 0 := by
  cases p with
  | zero => rfl
  | succ p => simp only [cin]; rw [if_neg (by simpa using h)]

theorem telescope (f : ℕ → ℤ) (n : ℕ) :
    ∑ p ∈ range n, f p = ∑ p ∈ range n, f (p + 1) - f n + f 0 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, sum_range_succ, ih]; ring

theorem ripple_value (n cm px py : ℕ) (hok : RippleOK n cm px py) (x y : ℕ → Bit) (hx : ZeroOff x px)
    (hy : ZeroOff y py) : ∃ k : ℤ, rowValue n x + rowValue n y = rowValue n (ripple cm x y) + 2 ^ n * k := by
  have hpos : ∀ p, p < n → ∃ k : ℤ, 2 ^ p * (iv (x p) + iv (y p) + iv (cin cm x y p)) =
      2 ^ p * iv (ripple cm x y p) + 2 ^ (p + 1) * iv (cin cm x y (p + 1)) + 2 ^ n * k := by
    intro p hp
    by_cases hc : bit cm p
    · refine ⟨0, ?_⟩
      simp only [ripple, cin, hc, if_true]
      rw [full_adder, pow_succ]
      ring
    · by_cases htop : p + 1 < n
      · refine ⟨0, ?_⟩
        have hcount : ¬ 2 ≤ (if bit px p then 1 else 0) + (if bit py p then 1 else 0) +
            (if 0 < p ∧ bit cm (p - 1) then 1 else 0) := fun h => hc (hok.covered p htop h)
        simp only [ripple, cin, hc, if_false, Bool.false_eq_true, iv_zero, mul_zero, add_zero]
        have hxv := hx p; have hyv := hy p
        have hcv := cin_zero cm x y p
        by_cases hcin : 0 < p ∧ bit cm (p - 1)
        · cases bx : bit px p <;> cases by' : bit py p <;> simp_all [iv_zero]
        · have := hcv hcin
          cases bx : bit px p <;> cases by' : bit py p <;> simp_all [iv_zero]
      · have hpn : p + 1 = n := by omega
        refine ⟨iv (maj (x p) (y p) (cin cm x y p)), ?_⟩
        simp only [ripple, cin, hc, if_false, Bool.false_eq_true, iv_zero, mul_zero, add_zero]
        rw [full_adder, ← hpn, pow_succ]
        ring
  let kk : ℕ → ℤ := fun p => if h : p < n then Classical.choose (hpos p h) else 0
  have hk : ∀ p ∈ range n, 2 ^ p * (iv (x p) + iv (y p) + iv (cin cm x y p)) =
      2 ^ p * iv (ripple cm x y p) + 2 ^ (p + 1) * iv (cin cm x y (p + 1)) + 2 ^ n * kk p := by
    intro p hp
    have hp' := mem_range.mp hp
    simp only [kk, dif_pos hp']
    exact Classical.choose_spec (hpos p hp')
  refine ⟨∑ p ∈ range n, kk p, ?_⟩
  have hlast : cin cm x y n = 0 := by
    cases n with
    | zero => rfl
    | succ m => exact cin_zero cm x y (m + 1) fun h => by have := hok.low m (by simpa using h.2); omega
  have htel := telescope (fun p => 2 ^ p * iv (cin cm x y p)) n
  have hsum := sum_congr rfl hk
  simp only [mul_add, sum_add_distrib] at hsum
  simp only [rowValue, mul_sum]
  rw [hlast, iv_zero, mul_zero] at htel
  simp only [show cin cm x y 0 = 0 from rfl, iv_zero, mul_zero, sub_zero, add_zero] at htel
  linarith

end LeanVMCircuits.Multiply
