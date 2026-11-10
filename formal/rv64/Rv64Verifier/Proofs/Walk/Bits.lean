import Rv64Verifier.Proofs.Rodata
import Rv64Verifier.Model.Multilinear

/-!
# `walk`: the bit tricks of `build_layout`'s head

`log2_strict`'s power-of-two test compiles to `x - 1 <ᵤ x ^ (x - 1)` (`pow2_word`), its
`trailing_zeros` to a de Bruijn multiply and a table in `.rodata` (`ctz_lookup`).
`log2_ceil`'s `leading_zeros` compiles to a smear (`smear_eq`) and a SWAR popcount (`pop_table`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 Rv64Verifier.Model

theorem two_pow_lt_succ (k : Nat) : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_succ (by decide)

theorem xor_pred_odd (k q : Nat) :
    (2 ^ (k + 1) * q + 2 ^ k) ^^^ (2 ^ (k + 1) * q + (2 ^ k - 1)) = 2 ^ (k + 1) - 1 := by
  have h1 := two_pow_lt_succ k
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ h1,
    Nat.testBit_two_pow_mul_add _ (by omega : 2 ^ k - 1 < 2 ^ (k + 1)), Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  by_cases hj : j < k + 1
  · simp only [hj, ↓reduceIte]
    by_cases hk : j = k
    · subst hk; simp
    · simp [show ¬ k = j by omega, show j < k by omega]
  · simp [hj]

theorem and_pred_odd (k q : Nat) :
    (2 ^ (k + 1) * q + 2 ^ k) &&& (2 ^ (k + 1) * q + (2 ^ k - 1)) = 2 ^ (k + 1) * q := by
  have h1 := two_pow_lt_succ k
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1,
    Nat.testBit_two_pow_mul_add _ (by omega : 2 ^ k - 1 < 2 ^ (k + 1)), Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow, ← Nat.add_zero (2 ^ (k + 1) * q),
    Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos _), Nat.zero_testBit]
  by_cases hj : j < k + 1
  · simp only [hj, ↓reduceIte]
    by_cases hk : j = k
    · subst hk; simp
    · simp [show ¬ k = j by omega]
  · simp only [hj, ↓reduceIte]
    exact Bool.and_self _

/-- The compiled power-of-two test, on numbers. -/
theorem pow2_nat {n : Nat} (hn : n ≠ 0) : n - 1 < n ^^^ (n - 1) ↔ n &&& (n - 1) = 0 := by
  obtain ⟨k, m, ⟨q, rfl⟩, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hp := Nat.one_le_two_pow (n := k)
  have hs : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
  have e1 : 2 ^ k * (2 * q + 1) = 2 ^ (k + 1) * q + 2 ^ k := by rw [hs]; ring
  have e2 : 2 ^ k * (2 * q + 1) - 1 = 2 ^ (k + 1) * q + (2 ^ k - 1) := by rw [e1]; omega
  rw [e2, e1, xor_pred_odd, and_pred_odd]
  rcases q with _ | q
  · simp only [Nat.mul_zero, Nat.zero_add]
    exact iff_of_true (by omega) trivial
  · rw [Nat.mul_succ]
    constructor
    · intro h; omega
    · intro h; omega

theorem sub_one_toNat {x : Word} (hn : x.toNat ≠ 0) : (x - 1).toNat = x.toNat - 1 := by
  have h1 : (1 : Word).toNat = 1 := rfl
  have := x.isLt
  rw [BitVec.toNat_sub, h1]
  omega

/-- The compiled power-of-two test: `x - 1 <ᵤ x ^ (x - 1)`. -/
theorem pow2_word (x : Word) :
    (x - 1).toNat < (x ^^^ (x - 1)).toNat ↔ x ≠ 0 ∧ x &&& (x - 1) = 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · have hn : x.toNat ≠ 0 := fun h ↦ hx (BitVec.eq_of_toNat_eq (by simpa using h))
    have hs : (x - 1).toNat = x.toNat - 1 := sub_one_toNat hn
    have ha : x &&& (x - 1) = 0 ↔ x.toNat &&& (x.toNat - 1) = 0 := by
      rw [← BitVec.toNat_inj, BitVec.toNat_and, hs]
      simp
    rw [BitVec.toNat_xor, hs, ha, pow2_nat hn]
    exact ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩

/-- A power of two is `2 ^ ctz`. -/
theorem pow2_ctz {x : Word} (hx : x ≠ 0) (hp : x &&& (x - 1) = 0) :
    x.toNat = 2 ^ x.ctz.toNat ∧ x.ctz.toNat < 64 := by
  have hn : x.toNat ≠ 0 := fun h ↦ hx (BitVec.eq_of_toNat_eq (by simpa using h))
  have hs : (x - 1).toNat = x.toNat - 1 := sub_one_toNat hn
  have hp' : x.toNat &&& (x.toNat - 1) = 0 := by
    rw [← hs, ← BitVec.toNat_and, hp]; rfl
  obtain ⟨k, hk⟩ := Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mp ⟨hn, hp'⟩
  have hbit := BitVec.getLsbD_true_ctz_of_ne_zero hx
  rw [BitVec.getLsbD, hk, Nat.testBit_two_pow] at hbit
  have hc : x.ctz.toNat = k := (by simpa using hbit : k = x.ctz.toNat).symm
  have hl := x.isLt
  rw [hk] at hl
  refine ⟨by rw [hc, hk], ?_⟩
  rw [hc]
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp hl

theorem log2StrictRust_of {x : Word} (hx : x ≠ 0) (hp : x &&& (x - 1) = 0) :
    log2StrictRust x = some x.ctz.toNat := by
  simp only [log2StrictRust]
  split_ifs with h
  · rfl
  · exact absurd ⟨hx, hp⟩ h

theorem log2StrictRust_none {x : Word} (h : ¬ (x ≠ 0 ∧ x &&& (x - 1) = 0)) :
    log2StrictRust x = none := by
  simp only [log2StrictRust]
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-! ## The de Bruijn table -/

/-- `trailing_zeros`' table index, plus the table's address. -/
def dbAddr (x : Word) : Word := (((x &&& (0 - x)) * 0x218a392cd3d5dbf) >>> 58) + 0xa0000028

/-- The table's eight doublewords. -/
def dbTable : List Word :=
  [1371360393187950848, 2887970683572066564, 3466977930743779589, 4118878400891002634,
    2819564631906584127, 4049075943739565328, 3977852904543816510, 4195993915870615101]

theorem db_table : ∀ k < 64, ∃ j < 8,
    dbAddr (BitVec.ofNat 64 (2 ^ k)) &&& 0xfffffffffffffff8 = 0xa0000028 + BitVec.ofNat 64 (8 * j) ∧
      (extractByte (dbTable.getD j 0) (dbAddr (BitVec.ofNat 64 (2 ^ k)) &&& 7).toNat).zeroExtend 64 =
        BitVec.ofNat 64 k := by
  decide +kernel

theorem db_words {u : MachineState} (h : RodataOk u) {j : Nat} (hj : j < 8) :
    u.getMem (0xa0000028 + BitVec.ofNat 64 (8 * j)) = dbTable.getD j 0 := by
  interval_cases j <;> exact h.word

/-- `trailing_zeros` of `2 ^ k`, as the code reads it from `.rodata`. -/
theorem ctz_lookup {u : MachineState} (h : RodataOk u) {k : Nat} (hk : k < 64) :
    (extractByte (u.getMem (dbAddr (BitVec.ofNat 64 (2 ^ k)) &&& 0xfffffffffffffff8))
      (dbAddr (BitVec.ofNat 64 (2 ^ k)) &&& 7).toNat).zeroExtend 64 = BitVec.ofNat 64 k := by
  obtain ⟨j, hj, e1, e2⟩ := db_table k hk
  rw [e1, db_words h hj, e2]

theorem db_const {u : MachineState} (h : RodataOk u) : u.getMem 0xa0000020 = 0x218a392cd3d5dbf :=
  h.word

/-! ## `leading_zeros`: smear and popcount -/

/-- Some bit of `y` among `i .. i + m`. -/
def Win (y : Word) (m i : Nat) : Prop := ∃ k < m, y.getLsbD (i + k) = true

theorem win_or {a y : Word} {m : Nat} (ha : ∀ i, a.getLsbD i = true ↔ Win y m i) (i : Nat) :
    (a ||| a >>> m).getLsbD i = true ↔ Win y (2 * m) i := by
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, Bool.or_eq_true, ha, ha]
  constructor
  · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩)
    · exact ⟨k, by omega, h⟩
    · exact ⟨m + k, by omega, by rwa [show i + (m + k) = m + i + k by omega]⟩
  · rintro ⟨k, hk, h⟩
    by_cases hkm : k < m
    · exact Or.inl ⟨k, hkm, h⟩
    · exact Or.inr ⟨k - m, by omega, by rwa [show m + i + (k - m) = i + k by omega]⟩

/-- `x |= x >> 1; x |= x >> 2; .. x |= x >> 32`. -/
def smear (y : Word) : Word :=
  let a := y ||| y >>> 1
  let a := a ||| a >>> 2
  let a := a ||| a >>> 4
  let a := a ||| a >>> 8
  let a := a ||| a >>> 16
  a ||| a >>> 32

theorem smear_win (y : Word) (i : Nat) : (smear y).getLsbD i = true ↔ Win y 64 i := by
  have h0 : ∀ i, y.getLsbD i = true ↔ Win y 1 i := fun i ↦
    ⟨fun h ↦ ⟨0, by omega, by simpa using h⟩, fun ⟨k, hk, h⟩ ↦ by
      obtain rfl : k = 0 := by omega
      simpa using h⟩
  have h1 : ∀ i, (y ||| y >>> 1).getLsbD i = true ↔ Win y 2 i := win_or h0
  have h2 := win_or h1
  have h3 := win_or h2
  have h4 := win_or h3
  have h5 := win_or h4
  exact win_or h5 i

theorem smear_eq (y : Word) : smear y = BitVec.allOnes 64 >>> y.clz.toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
  apply Bool.eq_iff_iff.mpr
  rw [smear_win, decide_eq_true_iff]
  by_cases hy : y = 0
  · subst hy
    have hc : (0#64).clz = 64#64 := BitVec.clz_eq_iff_eq_zero.mpr rfl
    rw [show (0 : Word) = 0#64 from rfl, hc]
    constructor
    · rintro ⟨k, -, h⟩; simp at h
    · intro h; simp at h
  · have hc := BitVec.getLsbD_true_clz_of_ne_zero (by decide) hy
    have hlt := BitVec.toNat_lt_two_pow_sub_clz (x := y)
    have hcl : y.clz.toNat < 64 := by
      have := BitVec.lt_def.mp (BitVec.clz_lt_iff_ne_zero.mpr hy)
      simpa using this
    constructor
    · rintro ⟨k, -, h⟩
      by_contra hn
      rw [BitVec.getLsbD, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt
        (Nat.pow_le_pow_right (by decide) (by omega)))] at h
      cases h
    · intro h
      exact ⟨63 - y.clz.toNat - i, by omega, by
        rw [show i + (63 - y.clz.toNat - i) = 64 - 1 - y.clz.toNat by omega]; exact hc⟩

/-- The SWAR popcount `count_ones` compiles to. -/
def popSwar (z : Word) : Word :=
  let a := z - ((z >>> 1) &&& 0x5555555555555555)
  let a := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let a := (a + (a >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  (a * 0x0101010101010101) >>> 56

theorem pop_table : ∀ c ≤ 64, popSwar (~~~(BitVec.allOnes 64 >>> c)) = BitVec.ofNat 64 c := by
  decide +kernel

/-- `leading_zeros` as compiled: the popcount of the smear's complement. -/
theorem pop_smear (y : Word) : popSwar (~~~(smear y)) = BitVec.ofNat 64 y.clz.toNat := by
  rw [smear_eq]
  exact pop_table _ (by have := BitVec.clz_le (x := y); simpa [BitVec.le_def] using this)

end Rv64Verifier.Proofs.Walk
