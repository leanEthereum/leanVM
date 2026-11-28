module

public import NativeRustc.Xmss.Model

/-!
# `is_codeword`'s bit counts as rustc computes them

rustc computes `is_codeword`'s two `u128::count_ones` on the digest's two 64-bit halves `lo`,
`hi` with SWAR popcounts (`popLowLo`, `popLowHi`, `popHighLo`, `popHighHi`): masks, shifts within
bytes, the sum of each byte's count, and the bytes summed by a multiplication by `0x0101…01`.
This module proves them the counts (`countOnes_low`, `countOnes_notLow`) and the test of the
digits past the 58th the test of `hi`'s top 12 bits (`shr116_eq_zero`).

The proofs read a 64-bit value as eight byte lanes (`lanes`): masks and shifts of lanes act on
each lane (`testBit_lanes`), sums and differences without carries or borrows are lane-wise
(`lanes_add`, `lanes_sub`), and the final multiplication sums them (`lanes_mul_sum`); each lane's
count is then checked on the 256 bytes.
-/

@[expose] public section

namespace NativeRustc.Xmss.Swar

/-! ## Byte lanes -/

/-- `n` byte lanes, little-endian: `f 0 + 256 f 1 + …`. -/
def lanes (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f 0 + 256 * lanes (fun j ↦ f (j + 1)) n

theorem lanes_succ (f : Nat → Nat) (n : Nat) :
    lanes f (n + 1) = 256 * lanes (fun j ↦ f (j + 1)) n + f 0 := by
  rw [lanes, Nat.add_comm]

theorem lanes_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ j < n, f j = g j) → lanes f n = lanes g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [lanes, lanes, h 0 (by omega), lanes_congr (n := n) fun j hj ↦ h (j + 1) (by omega)]

/-- The bits of lanes. -/
theorem testBit_lanes : ∀ {n : Nat} {f : Nat → Nat}, (∀ j < n, f j < 256) → ∀ i,
    (lanes f n).testBit i = (decide (i / 8 < n) && (f (i / 8)).testBit (i % 8))
  | 0, f, _, i => by simp [lanes]
  | n + 1, f, hf, i => by
    rw [lanes_succ, show (256 : Nat) = 2 ^ 8 from rfl,
      Nat.testBit_two_pow_mul_add _ (hf 0 (by omega))]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ↓reduceIte]
      rw [testBit_lanes (fun j hj ↦ hf (j + 1) (by omega))]
      have h1 : (i - 8) / 8 + 1 = i / 8 := by omega
      have h2 : (i - 8) % 8 = i % 8 := by omega
      rw [h1, h2]
      congr 1
      simp only [decide_eq_decide]
      omega

theorem lanes_lt : ∀ {n : Nat} {f : Nat → Nat}, (∀ j < n, f j < 256) → lanes f n < 256 ^ n
  | 0, _, _ => by simp [lanes]
  | n + 1, f, hf => by
    have := lanes_lt (n := n) (f := fun j ↦ f (j + 1)) fun j hj ↦ hf (j + 1) (by omega)
    have := hf 0 (by omega)
    rw [lanes, Nat.pow_succ]
    omega

theorem lanes_add : ∀ {n : Nat} (f g : Nat → Nat),
    lanes f n + lanes g n = lanes (fun j ↦ f j + g j) n
  | 0, _, _ => rfl
  | n + 1, f, g => by
    rw [lanes, lanes, lanes, ← lanes_add (n := n)]
    omega

theorem lanes_le : ∀ {n : Nat} {f g : Nat → Nat}, (∀ j < n, g j ≤ f j) → lanes g n ≤ lanes f n
  | 0, _, _, _ => le_rfl
  | n + 1, f, g, h => by
    have := lanes_le (n := n) (f := fun j ↦ f (j + 1)) (g := fun j ↦ g (j + 1))
      fun j hj ↦ h (j + 1) (by omega)
    have := h 0 (by omega)
    rw [lanes, lanes]
    omega

theorem lanes_sub : ∀ {n : Nat} {f g : Nat → Nat}, (∀ j < n, g j ≤ f j) →
    lanes f n - lanes g n = lanes (fun j ↦ f j - g j) n
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    have hle := lanes_le (n := n) (f := fun j ↦ f (j + 1)) (g := fun j ↦ g (j + 1))
      fun j hj ↦ h (j + 1) (by omega)
    have ih := lanes_sub (n := n) (f := fun j ↦ f (j + 1)) (g := fun j ↦ g (j + 1))
      fun j hj ↦ h (j + 1) (by omega)
    have := h 0 (by omega)
    rw [lanes, lanes, lanes, ← ih, Nat.mul_sub]
    have : 256 * lanes (fun j ↦ g (j + 1)) n ≤ 256 * lanes (fun j ↦ f (j + 1)) n :=
      Nat.mul_le_mul_left _ hle
    omega

/-- A mask of lanes. -/
theorem lanes_and {n : Nat} {f g : Nat → Nat} (hf : ∀ j < n, f j < 256)
    (hg : ∀ j < n, g j < 256) : lanes f n &&& lanes g n = lanes (fun j ↦ f j &&& g j) n := by
  have hfg : ∀ j < n, (f j &&& g j) < 256 := fun j hj ↦ Nat.and_lt_two_pow _ (n := 8) (hg j hj)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_lanes hf, testBit_lanes hg, testBit_lanes hfg, Nat.testBit_and]
  cases decide (i / 8 < n) <;> rfl

/-- A shift of lanes, masked so that no bit crosses a lane. -/
theorem lanes_shr_and {n k c : Nat} {f : Nat → Nat} (hf : ∀ j < n, f j < 256) (hc : c < 2 ^ (8 - k))
    (hk : k ≤ 8) : (lanes f n >>> k) &&& lanes (fun _ ↦ c) n = lanes (fun j ↦ (f j >>> k) &&& c) n := by
  have hc8 : c < 256 :=
    lt_of_lt_of_le hc (Nat.pow_le_pow_right (n := 2) (by omega) (show 8 - k ≤ 8 by omega))
  have hfg : ∀ j < n, ((f j >>> k) &&& c) < 256 := fun j _ ↦ Nat.and_lt_two_pow _ (n := 8) hc8
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_lanes hf, testBit_lanes (fun _ _ ↦ hc8),
    testBit_lanes hfg, Nat.testBit_and, Nat.testBit_shiftRight]
  by_cases hci : c.testBit (i % 8) = true
  · have hlt : i % 8 < 8 - k := by
      by_contra hn
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc
        (Nat.pow_le_pow_right (n := 2) (by omega) (show 8 - k ≤ i % 8 by omega)))] at hci
      exact Bool.false_ne_true hci
    have h1 : (k + i) / 8 = i / 8 := by omega
    have h2 : (k + i) % 8 = k + i % 8 := by omega
    rw [h1, h2, hci]
    by_cases hn : i / 8 < n <;> simp [hn]
  · simp only [Bool.not_eq_true] at hci
    simp [hci]

/-- A shift of lanes by `k ≤ 8` bits: each lane takes the low bits of the next. -/
theorem lanes_shr {n k : Nat} {f : Nat → Nat} (hf : ∀ j < n, f j < 256) (hn : f n = 0)
    (hk : k ≤ 8) :
    lanes f n >>> k = lanes (fun j ↦ f j >>> k + 2 ^ (8 - k) * (f (j + 1) % 2 ^ k)) n := by
  have hf' : ∀ j ≤ n, f j < 256 := fun j hj ↦ by
    rcases Nat.lt_or_eq_of_le hj with h | h
    · exact hf j h
    · rw [h, hn]; omega
  have hk8 : 2 ^ k * 2 ^ (8 - k) = 256 := by rw [← Nat.pow_add, show k + (8 - k) = 8 by omega]
  have hlt : ∀ j < n, f j >>> k < 2 ^ (8 - k) := fun j hj ↦ by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hk8]
    exact hf j hj
  have hg : ∀ j < n, f j >>> k + 2 ^ (8 - k) * (f (j + 1) % 2 ^ k) < 256 := fun j hj ↦ by
    have := Nat.mod_lt (f (j + 1)) (Nat.two_pow_pos k)
    have := hlt j hj
    have h2 := Nat.mul_le_mul_left (2 ^ (8 - k)) (show f (j + 1) % 2 ^ k + 1 ≤ 2 ^ k by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (2 ^ (8 - k)) (2 ^ k), hk8] at h2
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, testBit_lanes hf, testBit_lanes hg]
  have hlo : ∀ j < n, f j >>> k < 2 ^ (8 - k) := hlt
  by_cases hi : i / 8 < n
  · rw [Nat.add_comm (f (i / 8) >>> k), Nat.testBit_two_pow_mul_add _ (hlo _ hi)]
    by_cases ht : i % 8 < 8 - k
    · simp only [ht, ↓reduceIte]
      rw [Nat.testBit_shiftRight]
      have h1 : (k + i) / 8 = i / 8 := by omega
      have h2 : (k + i) % 8 = k + i % 8 := by omega
      simp [hi, h1, h2]
    · simp only [ht, ↓reduceIte]
      rw [Nat.testBit_mod_two_pow]
      have h1 : (k + i) / 8 = i / 8 + 1 := by omega
      have h2 : (k + i) % 8 = i % 8 - (8 - k) := by omega
      rw [h1, h2]
      have h3 : decide (i % 8 - (8 - k) < k) = true := by simp; omega
      rw [h3, Bool.true_and]
      by_cases hn1 : i / 8 + 1 < n
      · simp [hi, hn1]
      · have : i / 8 + 1 = n := by omega
        rw [this, hn]
        simp
  · have h1 : ¬ (k + i) / 8 < n := by omega
    simp [hi, h1]

/-- The multiplication by `0x0101…01` of eight lanes summing below 256: their sum in the top one. -/
theorem mul_sum8 (a b c d e f g h : Nat) (hs : a + b + c + d + e + f + g + h < 256) :
    (a + 256 * (b + 256 * (c + 256 * (d + 256 * (e + 256 * (f + 256 * (g + 256 * (h + 256 * 0)))))))) *
      0x0101010101010101 % 2 ^ 64 / 2 ^ 56 = a + b + c + d + e + f + g + h := by
  rw [show (a + 256 * (b + 256 * (c + 256 * (d + 256 * (e + 256 * (f + 256 * (g + 256 *
      (h + 256 * 0)))))))) * 0x0101010101010101 =
      (2 ^ 56 * (a + b + c + d + e + f + g + h) +
        (a + 256 * (a + b) + 65536 * (a + b + c) + 16777216 * (a + b + c + d) +
          4294967296 * (a + b + c + d + e) + 1099511627776 * (a + b + c + d + e + f) +
          281474976710656 * (a + b + c + d + e + f + g))) +
      2 ^ 64 * ((b + c + d + e + f + g + h) + 256 * (c + d + e + f + g + h) +
        65536 * (d + e + f + g + h) + 16777216 * (e + f + g + h) +
        4294967296 * (f + g + h) + 1099511627776 * (g + h) + 281474976710656 * h) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The multiplication by `0x0101…01` sums the lanes into the top one. -/
theorem lanes_mul_sum {f : Nat → Nat}
    (hs : f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 < 256) :
    lanes f 8 * 0x0101010101010101 % 2 ^ 64 / 2 ^ 56 =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 :=
  mul_sum8 _ _ _ _ _ _ _ _ hs

/-- A number below `256 ^ n` is its `n` byte lanes. -/
theorem eq_lanes : ∀ {n x : Nat}, x < 256 ^ n → x = lanes (fun j ↦ x / 256 ^ j % 256) n
  | 0, x, h => by simp at h; simp [lanes, h]
  | n + 1, x, h => by
    rw [lanes]
    have : x / 256 < 256 ^ n := by rw [Nat.pow_succ] at h; omega
    have ih := eq_lanes this
    have hc : lanes (fun j ↦ x / 256 / 256 ^ j % 256) n =
        lanes (fun j ↦ x / 256 ^ (j + 1) % 256) n :=
      lanes_congr fun j _ ↦ by rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    rw [← hc, ← ih]
    simp
    omega

/-! ## Counting bits -/

/-- The set bits among the low `n` of `x`. -/
def pop (x n : Nat) : Nat := ∑ i ∈ Finset.range n, (x.testBit i).toNat

/-- The count over `8 m` bits of lanes is the sum of the lanes' counts. -/
theorem pop_lanes : ∀ {m : Nat} {f : Nat → Nat}, (∀ j < m, f j < 256) →
    pop (lanes f m) (8 * m) = ∑ j ∈ Finset.range m, pop (f j) 8
  | 0, _, _ => rfl
  | m + 1, f, hf => by
    rw [pop, show 8 * (m + 1) = 8 + 8 * m by omega, Finset.sum_range_add,
      Finset.sum_range_succ' (fun j ↦ pop (f j) 8) m,
      Nat.add_comm (∑ j ∈ Finset.range m, pop (f (j + 1)) 8)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [testBit_lanes hf, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      simp
    · rw [← pop_lanes (fun j hj ↦ hf (j + 1) (by omega)), pop]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [testBit_lanes hf, testBit_lanes (fun j hj ↦ hf (j + 1) (by omega))]
      have h1 : (8 + i) / 8 = i / 8 + 1 := by omega
      have h2 : (8 + i) % 8 = i % 8 := by omega
      have h3 : decide (i / 8 + 1 < m + 1) = decide (i / 8 < m) := by
        simp only [decide_eq_decide]; omega
      rw [h1, h2, h3]

/-- The count over `w + n` bits of `2 ^ w h + l` is `l`'s over `w` and `h`'s over `n`. -/
theorem pop_split {w h l : Nat} (hl : l < 2 ^ w) (n : Nat) :
    pop (2 ^ w * h + l) (w + n) = pop l w + pop h n := by
  rw [pop, Finset.sum_range_add, pop, pop]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.testBit_two_pow_mul_add _ hl]
    simp [hi]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Nat.testBit_two_pow_mul_add _ hl]
    simp

/-- A mask of `2 ^ w h + l`. -/
theorem and_split {w h l h' l' : Nat} (hl : l < 2 ^ w) (hl' : l' < 2 ^ w) :
    (2 ^ w * h + l) &&& (2 ^ w * h' + l') = 2 ^ w * (h &&& h') + (l &&& l') := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hl, Nat.testBit_two_pow_mul_add _ hl',
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hl')]
  split <;> simp [Nat.testBit_and]

/-! ## rustc's popcounts -/

section
open BitVec

/-- `0x1111…`. -/
def m11 : BitVec 64 := 0x1111111111111111#64
/-- `0x3333…`. -/
def m33 : BitVec 64 := 0x3333333333333333#64
/-- `0x0f0f…`. -/
def m0f : BitVec 64 := 0x0f0f0f0f0f0f0f0f#64
/-- `0x0101…`. -/
def m01 : BitVec 64 := 0x0101010101010101#64
/-- `0xaaaa…`. -/
def maa : BitVec 64 := 0xaaaaaaaaaaaaaaaa#64
/-- `LOW` below bit 52. -/
def m55hi : BitVec 64 := 0x0005555555555555#64
/-- `!LOW` below bit 52. -/
def maahi : BitVec 64 := 0x000aaaaaaaaaaaaa#64
/-- The top 12 bits. -/
def mtop : BitVec 64 := 0xfff0000000000000#64

/-- The end of a popcount from per-byte nibble counts `s`. -/
def fromNibbles (s : BitVec 64) : BitVec 64 := (((s + (s >>> 4)) &&& m0f) * m01) >>> 56

/-- The end of a popcount from per-pair counts `a`. -/
def fromPairs (a : BitVec 64) : BitVec 64 :=
  fromNibbles ((a &&& m33) + ((a >>> 2) &&& m33))

/-- `(lo & LOW).count_ones()` as rustc computes it. -/
def popLowLo (lo : BitVec 64) : BitVec 64 := fromNibbles ((lo &&& m11) + ((lo >>> 2) &&& m11))

/-- `(hi & LOW).count_ones()` as rustc computes it. -/
def popLowHi (hi : BitVec 64) : BitVec 64 := fromPairs (hi &&& m55hi)

/-- `(lo & !LOW).count_ones()` as rustc computes it. -/
def popHighLo (lo : BitVec 64) : BitVec 64 := fromPairs ((lo &&& maa) - ((lo &&& maa) >>> 1))

/-- `(hi & !LOW).count_ones()` as rustc computes it. -/
def popHighHi (hi : BitVec 64) : BitVec 64 := fromPairs ((hi &&& maahi) - ((hi &&& maahi) >>> 1))

end

/-- A 64-bit value's byte `j`. -/
def byte (x : BitVec 64) (j : Nat) : Nat := x.toNat / 256 ^ j % 256

theorem byte_lt (x : BitVec 64) (j : Nat) : byte x j < 256 := Nat.mod_lt _ (by omega)

theorem byte_eight (x : BitVec 64) : byte x 8 = 0 := by
  unfold byte
  rw [Nat.div_eq_of_lt (by have := x.isLt; simpa using this)]

theorem toNat_lanes (x : BitVec 64) : x.toNat = lanes (byte x) 8 :=
  eq_lanes (by have := x.isLt; simpa using this)

theorem const_lanes (c : Nat) : lanes (fun _ ↦ c) 8 =
    c * 0x0101010101010101 := by simp only [lanes]; omega

/-- A lane function's value at lane `j` below 256. -/
theorem lanes_toNat {f : Nat → Nat} (hf : ∀ j < 8, f j < 256) :
    (BitVec.ofNat 64 (lanes f 8)).toNat = lanes f 8 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le (lanes_lt hf) (by decide)

/-- `fromNibbles` of lanes holding at most 4 in each nibble: the sum of the lanes' nibbles. -/
theorem fromNibbles_toNat {s : BitVec 64} {f : Nat → Nat} (hs : s.toNat = lanes f 8)
    (hf : ∀ j < 8, f j % 16 ≤ 4 ∧ f j / 16 ≤ 4) :
    (fromNibbles s).toNat = ∑ j ∈ Finset.range 8, (f j % 16 + f j / 16) := by
  set g : Nat → Nat := fun j ↦ if j < 8 then f j else 0 with hg
  have hgb : ∀ j, g j % 16 ≤ 4 ∧ g j / 16 ≤ 4 := fun j ↦ by
    by_cases h : j < 8
    · simpa [hg, h] using hf j h
    · simp [hg, h]
  have hg8 : ∀ j, g j < 256 := fun j ↦ by have := hgb j; omega
  have hs' : s.toNat = lanes g 8 := hs.trans (lanes_congr fun j hj ↦ by simp [hg, hj])
  have hshr : (s >>> 4).toNat = lanes (fun j ↦ g j >>> 4 + 2 ^ 4 * (g (j + 1) % 2 ^ 4)) 8 := by
    rw [BitVec.toNat_ushiftRight, hs', lanes_shr (fun j _ ↦ hg8 j) (by simp [hg]) (by omega)]
  have hb : ∀ j, g j + (g j >>> 4 + 2 ^ 4 * (g (j + 1) % 2 ^ 4)) < 256 := fun j ↦ by
    have := hgb j
    have := hgb (j + 1)
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hsum : (s + (s >>> 4)).toNat =
      lanes (fun j ↦ g j + (g j >>> 4 + 2 ^ 4 * (g (j + 1) % 2 ^ 4))) 8 := by
    rw [BitVec.toNat_add, hs', hshr, lanes_add, Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le (lanes_lt fun j _ ↦ hb j) (by decide)
  have hand : ((s + (s >>> 4)) &&& m0f).toNat = lanes (fun j ↦ f j % 16 + f j / 16) 8 := by
    rw [BitVec.toNat_and, hsum, show m0f.toNat = lanes (fun _ ↦ 15) 8 by rw [const_lanes]; rfl,
      lanes_and (fun j _ ↦ hb j) (fun _ _ ↦ by decide)]
    apply lanes_congr
    intro j hj
    have := hf j hj
    simp only [hg, hj, ↓reduceIte, Nat.shiftRight_eq_div_pow,
      show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  unfold fromNibbles
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, hand,
    show m01.toNat = 0x0101010101010101 from rfl, Nat.shiftRight_eq_div_pow, lanes_mul_sum]
  · simp [Finset.sum_range_succ]
  · have := hf 0 (by omega); have := hf 1 (by omega); have := hf 2 (by omega)
    have := hf 3 (by omega); have := hf 4 (by omega); have := hf 5 (by omega)
    have := hf 6 (by omega); have := hf 7 (by omega)
    omega

/-! ## Each byte's counts -/

/-- `popLowLo`'s byte: its nibbles count the even bits of their halves. -/
theorem byte_lowLo : ∀ b < 256, let f := (b &&& 0x11) + ((b >>> 2) &&& 0x11)
    f % 16 ≤ 4 ∧ f / 16 ≤ 4 ∧ f % 16 + f / 16 = pop (b &&& 0x55) 8 := by
  simp only [pop, Finset.sum_range_succ, Finset.sum_range_zero]
  decide +kernel

/-- `fromPairs`'s byte on the even bits. -/
theorem byte_lowPairs : ∀ b < 256, let g := b &&& 0x55
    let f := (g &&& 0x33) + ((g >>> 2) &&& 0x33)
    f % 16 ≤ 4 ∧ f / 16 ≤ 4 ∧ f % 16 + f / 16 = pop (b &&& 0x55) 8 := by
  simp only [pop, Finset.sum_range_succ, Finset.sum_range_zero]
  decide +kernel

/-- `fromPairs`'s byte on the odd bits, each moved down a place. -/
theorem byte_highPairs : ∀ b < 256, let g := (b &&& 0xaa) - (b &&& 0xaa) >>> 1
    let f := (g &&& 0x33) + ((g >>> 2) &&& 0x33)
    (b &&& 0xaa) >>> 1 ≤ b &&& 0xaa ∧ (b &&& 0xaa) % 2 = 0 ∧
      f % 16 ≤ 4 ∧ f / 16 ≤ 4 ∧ f % 16 + f / 16 = pop (b &&& 0xaa) 8 := by
  simp only [pop, Finset.sum_range_succ, Finset.sum_range_zero]
  decide +kernel

/-! ## The popcounts -/

theorem m11_lanes : m11.toNat = lanes (fun _ ↦ 0x11) 8 := by rw [const_lanes]; rfl
theorem m33_lanes : m33.toNat = lanes (fun _ ↦ 0x33) 8 := by rw [const_lanes]; rfl
theorem m55_lanes : (0x5555555555555555 : Nat) = lanes (fun _ ↦ 0x55) 8 := by rw [const_lanes]
theorem maa_lanes : maa.toNat = lanes (fun _ ↦ 0xaa) 8 := by rw [const_lanes]; rfl

theorem and_lt256 (x : Nat) {c : Nat} (hc : c < 256) : x &&& c < 256 :=
  Nat.and_lt_two_pow (n := 8) _ hc

/-- The count of `lanes f 8`'s bits is the sum of the lanes'. -/
theorem pop_lanes8 {f : Nat → Nat} (hf : ∀ j < 8, f j < 256) :
    pop (lanes f 8) 64 = ∑ j ∈ Finset.range 8, pop (f j) 8 := pop_lanes (m := 8) hf

/-- `fromPairs` of lanes `g` whose byte counts are `f`: the sum of the counts. -/
theorem fromPairs_toNat {a : BitVec 64} {g : Nat → Nat} (ha : a.toNat = lanes g 8)
    (hg : ∀ j < 8, g j < 256)
    (hf : ∀ j < 8, ((g j &&& 0x33) + ((g j >>> 2) &&& 0x33)) % 16 ≤ 4 ∧
      ((g j &&& 0x33) + ((g j >>> 2) &&& 0x33)) / 16 ≤ 4) :
    (fromPairs a).toNat = ∑ j ∈ Finset.range 8,
      (((g j &&& 0x33) + ((g j >>> 2) &&& 0x33)) % 16 +
        ((g j &&& 0x33) + ((g j >>> 2) &&& 0x33)) / 16) := by
  unfold fromPairs
  apply fromNibbles_toNat _ hf
  have h1 : (a &&& m33).toNat = lanes (fun j ↦ g j &&& 0x33) 8 := by
    rw [BitVec.toNat_and, ha, m33_lanes, lanes_and hg fun _ _ ↦ by decide]
  have h2 : ((a >>> 2) &&& m33).toNat = lanes (fun j ↦ (g j >>> 2) &&& 0x33) 8 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, ha, m33_lanes,
      lanes_shr_and hg (by decide) (by omega)]
  rw [BitVec.toNat_add, h1, h2, lanes_add, Nat.mod_eq_of_lt]
  refine lt_of_lt_of_le (lanes_lt fun j _ ↦ ?_) (by decide)
  have := and_lt256 (g j) (show 0x33 < 256 by decide)
  have : (g j &&& 0x33) ≤ 0x33 := Nat.and_le_right
  have : ((g j >>> 2) &&& 0x33) ≤ 0x33 := Nat.and_le_right
  omega

/-- **`(lo & LOW).count_ones()`**, rustc's way. -/
theorem popLowLo_toNat (x : BitVec 64) :
    (popLowLo x).toNat = pop (x.toNat &&& 0x5555555555555555) 64 := by
  have hb := byte_lt x
  rw [m55_lanes, toNat_lanes x, lanes_and (fun j _ ↦ hb j) (fun _ _ ↦ by decide),
    pop_lanes8 fun j _ ↦ and_lt256 _ (by decide), popLowLo]
  rw [fromNibbles_toNat (f := fun j ↦ (byte x j &&& 0x11) + ((byte x j >>> 2) &&& 0x11))]
  · exact Finset.sum_congr rfl fun j _ ↦ (byte_lowLo _ (hb j)).2.2
  · rw [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ushiftRight,
      m11_lanes, toNat_lanes x, lanes_and (fun j _ ↦ hb j) (fun _ _ ↦ by decide),
      lanes_shr_and (fun j _ ↦ hb j) (by decide) (by omega), lanes_add, Nat.mod_eq_of_lt]
    refine lt_of_lt_of_le (lanes_lt fun j _ ↦ ?_) (by decide)
    have : (byte x j &&& 0x11) ≤ 0x11 := Nat.and_le_right
    have : ((byte x j >>> 2) &&& 0x11) ≤ 0x11 := Nat.and_le_right
    omega
  · exact fun j _ ↦ ⟨(byte_lowLo _ (hb j)).1, (byte_lowLo _ (hb j)).2.1⟩

/-- `fromPairs` of the even bits: their count. -/
theorem fromPairs_low (x : BitVec 64) :
    (fromPairs (x &&& 0x5555555555555555#64)).toNat = pop (x.toNat &&& 0x5555555555555555) 64 := by
  have hb := byte_lt x
  have ha : (x &&& 0x5555555555555555#64).toNat = lanes (fun j ↦ byte x j &&& 0x55) 8 := by
    rw [BitVec.toNat_and,
      show (0x5555555555555555#64).toNat = lanes (fun _ ↦ 0x55) 8 by rw [const_lanes]; rfl,
      toNat_lanes x, lanes_and (fun j _ ↦ hb j) (fun _ _ ↦ by decide)]
  rw [fromPairs_toNat ha, m55_lanes, toNat_lanes x,
    lanes_and (fun j _ ↦ hb j) (fun _ _ ↦ by decide), pop_lanes8 fun j _ ↦ and_lt256 _ (by decide)]
  · exact Finset.sum_congr rfl fun j _ ↦ (byte_lowPairs _ (hb j)).2.2
  · exact fun j _ ↦ and_lt256 _ (by decide)
  · exact fun j _ ↦ ⟨(byte_lowPairs _ (hb j)).1, (byte_lowPairs _ (hb j)).2.1⟩

/-- `fromPairs` of the odd bits moved down: their count. -/
theorem fromPairs_high (x : BitVec 64) :
    (fromPairs ((x &&& maa) - ((x &&& maa) >>> 1))).toNat =
      pop (x.toNat &&& 0xaaaaaaaaaaaaaaaa) 64 := by
  have hb := byte_lt x
  have hA : (x &&& maa).toNat = lanes (fun j ↦ byte x j &&& 0xaa) 8 := by
    rw [BitVec.toNat_and, maa_lanes, toNat_lanes x, lanes_and (fun j _ ↦ hb j) (fun _ _ ↦ by decide)]
  have hS : ((x &&& maa) >>> 1).toNat = lanes (fun j ↦ (byte x j &&& 0xaa) >>> 1) 8 := by
    rw [BitVec.toNat_ushiftRight, hA,
      lanes_shr (fun j _ ↦ and_lt256 _ (by decide)) (by rw [byte_eight]; rfl) (by omega)]
    apply lanes_congr
    intro j _
    simp [(byte_highPairs _ (hb (j + 1))).2.1]
  rw [show (0xaaaaaaaaaaaaaaaa : Nat) = lanes (fun _ ↦ 0xaa) 8 by rw [const_lanes],
    toNat_lanes x, lanes_and (fun j _ ↦ hb j) (fun _ _ ↦ by decide),
    pop_lanes8 fun j _ ↦ and_lt256 _ (by decide)]
  rw [fromPairs_toNat (g := fun j ↦ (byte x j &&& 0xaa) - (byte x j &&& 0xaa) >>> 1)]
  · exact Finset.sum_congr rfl fun j _ ↦ (byte_highPairs _ (hb j)).2.2.2.2
  · have hle : lanes (fun j ↦ (byte x j &&& 0xaa) >>> 1) 8 ≤ lanes (fun j ↦ byte x j &&& 0xaa) 8 :=
      lanes_le fun j _ ↦ (byte_highPairs _ (hb j)).1
    rw [BitVec.toNat_sub, hA, hS, ← lanes_sub fun j _ ↦ (byte_highPairs _ (hb j)).1]
    have := lanes_lt (n := 8) (f := fun j ↦ byte x j &&& 0xaa) fun j _ ↦ and_lt256 _ (by decide)
    have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
    rw [h64] at this
    omega
  · exact fun j _ ↦ lt_of_le_of_lt (Nat.sub_le _ _) (and_lt256 _ (by decide))
  · exact fun j _ ↦ ⟨(byte_highPairs _ (hb j)).2.2.1, (byte_highPairs _ (hb j)).2.2.2.1⟩

/-! ## `is_codeword` -/

theorem pop_le (x n : Nat) : pop x n ≤ n := by
  unfold pop
  calc ∑ i ∈ Finset.range n, (x.testBit i).toNat ≤ ∑ _i ∈ Finset.range n, 1 :=
        Finset.sum_le_sum fun i _ ↦ Bool.toNat_le _
    _ = n := by simp

theorem low_split : low = 2 ^ 64 * 0x5555555555555555 + 0x5555555555555555 := by decide +kernel

theorem notLow_split : notLow = 2 ^ 64 * 0xaaaaaaaaaaaaaaaa + 0xaaaaaaaaaaaaaaaa := by
  decide +kernel

/-- The masks below bit 52 agree with the full ones on a value below `2 ^ 52`. -/
theorem and_below52 (hi : BitVec 64) (h : hi.toNat < 2 ^ 52) {c c' : BitVec 64}
    (hc : ∀ i < 52, c.toNat.testBit i = c'.toNat.testBit i) : hi &&& c = hi &&& c' := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_and]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and]
  by_cases hi52 : i < 52
  · rw [hc i hi52]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))]
    rfl

theorem popLowHi_toNat (hi : BitVec 64) (h : hi.toNat < 2 ^ 52) :
    (popLowHi hi).toNat = pop (hi.toNat &&& 0x5555555555555555) 64 := by
  rw [popLowHi, and_below52 hi h (c' := 0x5555555555555555#64) (by decide +kernel), fromPairs_low]

theorem popHighLo_toNat (lo : BitVec 64) :
    (popHighLo lo).toNat = pop (lo.toNat &&& 0xaaaaaaaaaaaaaaaa) 64 := fromPairs_high lo

theorem popHighHi_toNat (hi : BitVec 64) (h : hi.toNat < 2 ^ 52) :
    (popHighHi hi).toNat = pop (hi.toNat &&& 0xaaaaaaaaaaaaaaaa) 64 := by
  rw [popHighHi, and_below52 hi h (c' := maa) (by decide +kernel), fromPairs_high]

/-- **`is_codeword` of a digest whose top 12 bits are zero**, as rustc computes it. -/
theorem isCodeword_swar (lo hi : BitVec 64) (h : hi.toNat < 2 ^ 52) :
    isCodeword (2 ^ 64 * hi.toNat + lo.toNat) =
      ((popLowLo lo).toNat + (popLowHi hi).toNat +
        2 * ((popHighLo lo).toNat + (popHighHi hi).toNat) == 106) := by
  have hlo := lo.isLt
  unfold isCodeword countOnes
  rw [popLowLo_toNat, popLowHi_toNat hi h, popHighLo_toNat, popHighHi_toNat hi h, low_split,
    notLow_split, and_split hlo (by decide), and_split hlo (by decide)]
  have h1 := pop_split (w := 64) (h := hi.toNat &&& 0x5555555555555555)
    (Nat.and_lt_two_pow 0x5555555555555555 hlo) 64
  have h2 := pop_split (w := 64) (h := hi.toNat &&& 0xaaaaaaaaaaaaaaaa)
    (Nat.and_lt_two_pow 0xaaaaaaaaaaaaaaaa hlo) 64
  rw [Nat.and_comm 0x5555555555555555, Nat.and_comm 0xaaaaaaaaaaaaaaaa] at *
  simp only [pop, Nat.reduceAdd] at h1 h2
  rw [h1, h2]
  have hz : (2 ^ 64 * hi.toNat + lo.toNat) >>> 116 = 0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]
  simp only [hz, beq_self_eq_true, Bool.true_and, pop]

/-- A digest with a top bit set is not a codeword. -/
theorem isCodeword_top (lo hi : BitVec 64) (h : ¬ hi.toNat < 2 ^ 52) :
    isCodeword (2 ^ 64 * hi.toNat + lo.toNat) = false := by
  unfold isCodeword
  have : (2 ^ 64 * hi.toNat + lo.toNat) >>> 116 ≠ 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    have := lo.isLt
    intro h0
    rw [Nat.div_eq_zero_iff_lt (by positivity)] at h0
    omega
  rw [show ((2 ^ 64 * hi.toNat + lo.toNat) >>> 116 == 0) = false from beq_false_of_ne this,
    Bool.false_and]

end NativeRustc.Xmss.Swar
