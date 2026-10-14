module

public import Mathlib.Tactic

@[expose] public section

/-!
RV64IM's multiplications and divisions, on register values as naturals below `2^64`, transcribed from the RISC-V
unprivileged ISA's M extension: `MUL`, `MULW`, `MULH`, `MULHSU`, `MULHU`, `DIV`, `DIVU`, `REM`, `REMU` and their word
forms, a zero divisor and the signed overflow as its table defines them.
-/

namespace LeanVMCircuits.Rv64

/-- The two's complement value of an `L`-bit pattern. -/
def signed (L x : ℕ) : ℤ := if x < 2 ^ (L - 1) then x else (x : ℤ) - 2 ^ L

/-- The `L`-bit pattern of an integer. -/
def bits (L : ℕ) (z : ℤ) : ℕ := (z % 2 ^ L).toNat

/-- A 32-bit result, sign-extended to 64 bits. -/
def sext32 (x : ℕ) : ℕ := bits 64 (signed 32 (x % 2 ^ 32))

/-- `MUL`, or `MULW`: the low 32 bits of the low words' product, sign-extended. -/
def mul (word : Bool) (a b : ℕ) : ℕ :=
  if word then sext32 ((a % 2 ^ 32) * (b % 2 ^ 32)) else a * b % 2 ^ 64

/-- An operand of a high multiplication: signed or unsigned. -/
def operand (isSigned : Bool) (x : ℕ) : ℤ := if isSigned then signed 64 x else x

/-- `MULH`, `MULHSU`, `MULHU`: the high 64 bits of the 128-bit product. -/
def mulh (signed1 signed2 : Bool) (a b : ℕ) : ℕ := bits 64 ((operand signed1 a * operand signed2 b) / 2 ^ 64)

/-- An `L`-bit division's quotient or remainder: a zero divisor gives all ones or the dividend, the signed overflow
`-2^(L-1) / -1` gives the dividend or zero, and otherwise the quotient rounds toward zero. -/
def divRem (L : ℕ) (isSigned rem : Bool) (a b : ℕ) : ℤ :=
  if isSigned then
    let x := signed L a
    let y := signed L b
    if y = 0 then (if rem then x else -1)
    else if x = -2 ^ (L - 1) ∧ y = -1 then (if rem then 0 else x)
    else if rem then x.tmod y else x.tdiv y
  else if b = 0 then (if rem then a else 2 ^ L - 1)
  else if rem then (a % b : ℕ) else (a / b : ℕ)

/-- `DIV`, `DIVU`, `REM`, `REMU`, or their word forms on the low 32 bits, the result sign-extended. -/
def div (isSigned rem word : Bool) (a b : ℕ) : ℕ :=
  if word then sext32 (bits 32 (divRem 32 isSigned rem (a % 2 ^ 32) (b % 2 ^ 32)))
  else bits 64 (divRem 64 isSigned rem a b)

end LeanVMCircuits.Rv64

/-!
What the circuits compute, on naturals: the arithmetic the gates' specifications compose to.
-/

namespace LeanVMCircuits.MulDiv

/-- `x`, or `2^64 - x` modulo `2^64`. -/
def negIf (neg : Bool) (x : ℕ) : ℕ := if neg then (2 ^ 64 - x) % 2 ^ 64 else x

/-- Bits 32 to 63 replaced by bit 31. -/
def sextIf (word : Bool) (x : ℕ) : ℕ := if word then Rv64.sext32 (x % 2 ^ 32) else x

/-- A division's operand: a word division's low 32 bits, extended as the division is signed or not. -/
def extend (isSigned word : Bool) (x : ℕ) : ℕ :=
  if word then (if isSigned then Rv64.sext32 (x % 2 ^ 32) else x % 2 ^ 32) else x

/-- Whether a signed division's operand is negative. -/
def negative (isSigned : Bool) (x : ℕ) : Bool := isSigned && decide (2 ^ 63 ≤ x)

/-- The magnitude of an operand. -/
def magnitude (isSigned : Bool) (x : ℕ) : ℕ := negIf (negative isSigned x) x

/-- The division circuit's result, from the magnitudes' quotient and remainder. -/
def divOut (isSigned rem word : Bool) (a b : ℕ) : ℕ :=
  let n := extend isSigned word a
  let d := extend isSigned word b
  let nn := negative isSigned n
  let dn := negative isSigned d
  let N := magnitude isSigned n
  let D := magnitude isSigned d
  sextIf word (if d = 0 then (if rem then n else 2 ^ 64 - 1)
    else if rem then negIf nn (N % D) else negIf (nn != dn) (N / D))

/-- The high multiplication circuit's result: the unsigned high word, less the other operand for each signed negative
one, modulo `2^64`. -/
def mulhOut (signed1 signed2 : Bool) (a b : ℕ) : ℕ :=
  let high := a * b / 2 ^ 64
  let high := (high + (if negative signed1 a then 2 ^ 64 - 1 - b + 1 else 0)) % 2 ^ 64
  (high + (if negative signed2 b then 2 ^ 64 - 1 - a + 1 else 0)) % 2 ^ 64

/-! Helpers for the proofs. -/

/-- A division operand's value at width `L`: two's complement or unsigned. -/
def opnd (L : ℕ) (s : Bool) (x : ℕ) : ℤ := if s then Rv64.signed L x else x

/-- Division rounding toward zero, a zero divisor giving the dividend or `-1`, without the overflow case. -/
def divCore (rem : Bool) (x y : ℤ) : ℤ :=
  if y = 0 then (if rem then x else -1) else if rem then x.tmod y else x.tdiv y

theorem sext32_mod (x : ℕ) : Rv64.sext32 (x % 2 ^ 32) = Rv64.sext32 x := by
  simp only [Rv64.sext32, Nat.mod_mod]

theorem bits64_lt (z : ℤ) : Rv64.bits 64 z < 2 ^ 64 := by
  unfold Rv64.bits; omega

theorem bits64_of_lt (x : ℕ) (hx : x < 2 ^ 64) : Rv64.bits 64 x = x := by
  unfold Rv64.bits; omega

theorem bits64_mod32 (z : ℤ) : Rv64.bits 64 z % 2 ^ 32 = Rv64.bits 32 z := by
  unfold Rv64.bits; omega

theorem bits64_signed64 (x : ℕ) (hx : x < 2 ^ 64) : Rv64.bits 64 (Rv64.signed 64 x) = x := by
  unfold Rv64.bits Rv64.signed; split_ifs <;> omega

theorem signed64_sext32 (x : ℕ) (hx : x < 2 ^ 32) : Rv64.signed 64 (Rv64.sext32 x) = Rv64.signed 32 x := by
  unfold Rv64.sext32 Rv64.signed Rv64.bits
  rw [Nat.mod_eq_of_lt hx]
  split_ifs <;> omega

theorem negIf_eq (b : Bool) (x : ℕ) (hx : x < 2 ^ 64) :
    negIf b x = Rv64.bits 64 (if b then -(x : ℤ) else x) := by
  unfold negIf Rv64.bits
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]; omega
  · simp only [↓reduceIte]; omega

/-- A signed operand is its sign applied to its magnitude, at most `2^63`, zero only for zero. -/
theorem magnitude_spec (n : ℕ) (hn : n < 2 ^ 64) :
    Rv64.signed 64 n = (if negative true n then -(magnitude true n : ℤ) else magnitude true n) ∧
      magnitude true n ≤ 2 ^ 63 ∧ (magnitude true n = 0 ↔ n = 0) := by
  unfold magnitude negative negIf Rv64.signed
  simp only [show (64 : ℕ) - 1 = 63 from rfl, Bool.true_and, decide_eq_true_eq]
  split_ifs <;> omega

theorem operand_eq (s : Bool) (x : ℕ) (hx : x < 2 ^ 64) :
    Rv64.operand s x = x - 2 ^ 64 * (if negative s x then 1 else 0) := by
  cases s
  · simp [Rv64.operand, negative]
  · simp only [Rv64.operand, negative, Rv64.signed, Bool.true_and, ↓reduceIte,
      show (64 : ℕ) - 1 = 63 from rfl, decide_eq_true_eq]
    split_ifs <;> omega

theorem extend_lt (s w : Bool) (x : ℕ) (hx : x < 2 ^ 64) : extend s w x < 2 ^ 64 := by
  unfold extend Rv64.sext32
  split_ifs
  · exact bits64_lt _
  · omega
  · exact hx

theorem opnd_extend (s : Bool) (x : ℕ) : opnd 64 s (extend s true x) = opnd 32 s (x % 2 ^ 32) := by
  cases s
  · simp [opnd, extend]
  · simp only [opnd, extend, ↓reduceIte]
    exact signed64_sext32 _ (Nat.mod_lt _ (by norm_num))

/-- An `L`-bit division's bits agree with `divCore`'s: the signed overflow's results are congruent. -/
theorem divRem_bits (L : ℕ) (hL : 0 < L) (s rem : Bool) (a b : ℕ) :
    Rv64.bits L (Rv64.divRem L s rem a b) = Rv64.bits L (divCore rem (opnd L s a) (opnd L s b)) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  unfold Rv64.divRem divCore opnd
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hb : b = 0
    · subst hb
      cases rem
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
        unfold Rv64.bits
        congr 1
        rw [show (2 : ℤ) ^ (k + 1) - 1 = -1 + 2 ^ (k + 1) * 1 by ring, Int.add_mul_emod_self_left]
      · simp
    · have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast hb
      simp only [if_neg hb, if_neg hb']
      cases rem <;> simp [← Int.ofNat_tmod]
  · simp only [↓reduceIte]
    by_cases hy : Rv64.signed (k + 1) b = 0
    · simp [hy]
    · simp only [if_neg hy]
      by_cases ho : Rv64.signed (k + 1) a = -2 ^ (k + 1 - 1) ∧ Rv64.signed (k + 1) b = -1
      · rw [if_pos ho]
        obtain ⟨h1, h2⟩ := ho
        rw [h1, h2]
        cases rem
        · simp only [Bool.false_eq_true, ↓reduceIte, Int.tdiv_neg, Int.tdiv_one, neg_neg,
            Nat.add_sub_cancel]
          unfold Rv64.bits
          congr 1
          rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, show -(2 : ℤ) ^ k - 2 ^ k = -2 ^ (k + 1) by ring]
          simp
        · simp [Int.tmod_neg, Int.tmod_one]
      · rw [if_neg ho]

/-- The division circuit's selection, before the word sign extension, is `divCore`'s 64-bit pattern. -/
theorem body_eq (s rem : Bool) (n d : ℕ) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) :
    (if d = 0 then (if rem then n else 2 ^ 64 - 1)
      else if rem then negIf (negative s n) (magnitude s n % magnitude s d)
      else negIf (negative s n != negative s d) (magnitude s n / magnitude s d))
      = Rv64.bits 64 (divCore rem (opnd 64 s n) (opnd 64 s d)) := by
  cases s
  · have e1 : ∀ x, negative false x = false := fun _ => rfl
    have e2 : ∀ x, magnitude false x = x := fun _ => rfl
    simp only [e1, e2, negIf, opnd, divCore, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
    by_cases hz : d = 0
    · subst hz
      cases rem
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
        unfold Rv64.bits; omega
      · simp only [↓reduceIte, Nat.cast_zero]
        exact (bits64_of_lt n hn).symm
    · have hz' : (d : ℤ) ≠ 0 := by exact_mod_cast hz
      simp only [if_neg hz, if_neg hz']
      cases rem
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← Int.ofNat_tdiv, bits64_of_lt _ (lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
      · simp only [↓reduceIte]
        rw [← Int.ofNat_tmod, bits64_of_lt _ (lt_of_le_of_lt (Nat.mod_le _ _) hn)]
  · obtain ⟨hxn, hNn, -⟩ := magnitude_spec n hn
    obtain ⟨hxd, hNd, hd0⟩ := magnitude_spec d hd
    simp only [opnd, ↓reduceIte]
    by_cases hz : d = 0
    · subst hz
      have h0 : Rv64.signed 64 0 = 0 := by norm_num [Rv64.signed]
      simp only [↓reduceIte, divCore, h0]
      cases rem
      · simp only [Bool.false_eq_true, ↓reduceIte]
        unfold Rv64.bits; omega
      · simp only [↓reduceIte]
        exact (bits64_signed64 n hn).symm
    · have hy : Rv64.signed 64 d ≠ 0 := by rw [hxd]; split_ifs <;> omega
      rw [if_neg hz]
      simp only [divCore, if_neg hy]
      rw [hxn, hxd]
      have hD : magnitude true d ≠ 0 := fun h => hz (hd0.mp h)
      generalize negative true n = p
      generalize negative true d = q
      generalize magnitude true n = N at *
      generalize magnitude true d = D at *
      have hm : N % D < 2 ^ 64 := lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
      have hq : N / D < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      cases rem
      · rw [negIf_eq _ _ hq]
        cases p <;> cases q <;>
          simp [Int.neg_tdiv, Int.tdiv_neg]
      · rw [negIf_eq _ _ hm]
        cases p <;> cases q <;>
          simp [Int.neg_tmod, Int.tmod_neg, ← Int.ofNat_tmod]

theorem mul_eq (word : Bool) (a b : ℕ) : sextIf word (a * b % 2 ^ 64) = Rv64.mul word a b := by
  cases word
  · simp [sextIf, Rv64.mul]
  · simp only [sextIf, Rv64.mul, ↓reduceIte]
    rw [← sext32_mod (a % 2 ^ 32 * (b % 2 ^ 32)), Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64),
      ← Nat.mul_mod]

theorem mulh_eq (signed1 signed2 : Bool) (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    mulhOut signed1 signed2 a b = Rv64.mulh signed1 signed2 a b := by
  unfold Rv64.mulh Rv64.bits mulhOut
  rw [operand_eq _ _ ha, operand_eq _ _ hb]
  have key : ∀ e1 e2 : ℤ, ((a : ℤ) - 2 ^ 64 * e1) * ((b : ℤ) - 2 ^ 64 * e2) =
      ((a * b : ℕ) : ℤ) + 2 ^ 64 * (2 ^ 64 * e1 * e2 - e1 * b - e2 * a) := by
    intros; push_cast; ring
  rw [key, Int.add_mul_ediv_left _ _ (by norm_num)]
  generalize negative signed1 a = p
  generalize negative signed2 b = q
  generalize a * b = m
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem div_eq (isSigned rem word : Bool) (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    divOut isSigned rem word a b = Rv64.div isSigned rem word a b := by
  unfold divOut Rv64.div
  dsimp only
  rw [body_eq _ _ _ _ (extend_lt _ _ _ ha) (extend_lt _ _ _ hb)]
  cases word
  · have e : ∀ x, extend isSigned false x = x := fun _ => rfl
    simp only [sextIf, Bool.false_eq_true, ↓reduceIte, e]
    rw [divRem_bits 64 (by norm_num)]
  · simp only [sextIf, ↓reduceIte]
    rw [bits64_mod32, opnd_extend, opnd_extend, divRem_bits 32 (by norm_num)]

end LeanVMCircuits.MulDiv
