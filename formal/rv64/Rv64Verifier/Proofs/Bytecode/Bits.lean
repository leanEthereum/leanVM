import Rv64Verifier.Proofs.Bytecode.Basic
import Rv64Verifier.Model.Bytecode

/-!
# Word facts `evaluate`'s code relies on

* The byte buckets: the eight ways the code extracts byte `k` of a word, plus `256 k`
  (`byteIdx*`), are `256 k + ((toLeBytes w).getD k 0).toNat`.
* A `u128` shifted left by `k < 64`, as two words (`shl128_lo`, `shl128_hi`): the low word is the
  word shifted, the high word the word shifted right by `64 - k`, as `(x >>> 1) >>> (63 - k)`.
* The bit masks of `bucket_step`: `(x <<< (63 - b)) >>>ₛ 63` is `-(bit b of x)`
  (`bitMask_eq`); the byte of a bucket (`bucketByte`).
* A halfword load at any even address (`step_lhu`), which the executor only does at an 8-aligned
  base.
-/

namespace Rv64Verifier.Proofs.Bytecode
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Model

/-! ## Bytes of a word -/

theorem toNat_toLeBytes (w : BitVec 64) {k : Nat} (hk : k < 8) :
    ((toLeBytes w).getD k 0).toNat = w.toNat / 2 ^ (8 * k) % 256 := by
  rw [getD_toLeBytes w hk, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_and255 (w : Word) : (w &&& 255).toNat = w.toNat % 256 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 8

theorem toNat_mul_shr (w : Word) (k : Nat) (hk : k < 8) :
    ((w * BitVec.ofNat 64 (2 ^ (56 - 8 * k))) >>> 56).toNat = w.toNat / 2 ^ (8 * k) % 256 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hp : 2 ^ (56 - 8 * k) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
  have h1 : 2 ^ (56 - 8 * k) % 2 ^ 64 = 2 ^ (56 - 8 * k) := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have hmod : w.toNat * 2 ^ (56 - 8 * k) % 2 ^ 64 = w.toNat % 2 ^ (8 * k + 8) * 2 ^ (56 - 8 * k) := by
    have e : (2 : Nat) ^ 64 = 2 ^ (8 * k + 8) * 2 ^ (56 - 8 * k) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [e, Nat.mul_mod_mul_right]
  have e56 : (2 : Nat) ^ 56 = 2 ^ (8 * k) * 2 ^ (56 - 8 * k) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hmod, e56, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _), Nat.pow_add,
    Nat.mod_mul_right_div_self]

theorem toNat_shr56 (w : Word) : (w >>> 56).toNat = w.toNat / 2 ^ (8 * 7) % 256 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

theorem toNat_signExtend_small (x : BitVec 32) (h : x.toNat < 2 ^ 31) :
    (x.signExtend 64).toNat = x.toNat := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false, BitVec.toNat_setWidth]
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [BitVec.msb_eq_toNat]; simp only [decide_eq_false_iff_not]; omega

theorem toNat_srlw24 (w : Word) :
    ((wordResult .srl (w.truncate 32) ((24 : Word).truncate 32)).signExtend 64).toNat =
      w.toNat / 2 ^ (8 * 3) % 256 := by
  have h : (wordResult .srl (w.truncate 32) ((24 : Word).truncate 32)).toNat = w.toNat % 2 ^ 32 / 2 ^ 24 := by
    simp only [wordResult, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    rfl
  rw [toNat_signExtend_small _ (by rw [h]; omega), h]
  omega

/-- `addiw x, c` of a small `x` and a small `c`. -/
theorem toNat_addw (x c : Word) (h : x.toNat + c.toNat < 2 ^ 31) :
    ((wordResult .add (x.truncate 32) (c.truncate 32)).signExtend 64).toNat = x.toNat + c.toNat := by
  have hs : (wordResult .add (x.truncate 32) (c.truncate 32)).toNat = x.toNat + c.toNat := by
    simp only [wordResult, BitVec.toNat_add, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    omega
  rw [toNat_signExtend_small _ (by rw [hs]; omega), hs]

/-! ## A `u128` shifted -/

theorem extractLsb'_xor128 (a b : BitVec 128) (i n : Nat) :
    (a ^^^ b).extractLsb' i n = a.extractLsb' i n ^^^ b.extractLsb' i n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [hj]

theorem shl128_lo (x : BitVec 64) (k : Nat) :
    (x.setWidth 128 <<< k).extractLsb' 0 64 = x <<< k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    Nat.shiftRight_zero]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 128), Nat.mod_mod_of_dvd _ (by decide : 2 ^ 64 ∣ 2 ^ 128)]

theorem shl128_hi (x : BitVec 64) {k : Nat} (hk : k < 64) :
    (x.setWidth 128 <<< k).extractLsb' 64 64 = (x >>> 1) >>> (63 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ushiftRight]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  have hb : x.toNat * 2 ^ k < 2 ^ 128 := by
    calc x.toNat * 2 ^ k < 2 ^ 64 * 2 ^ 64 :=
          Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
            (Nat.two_pow_pos _)
      _ = 2 ^ 128 := by norm_num
  have h1 : x.toNat / 2 ^ 1 / 2 ^ (63 - k) = x.toNat / 2 ^ (64 - k) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 2
    omega
  have h2 : x.toNat * 2 ^ k / 2 ^ 64 = x.toNat / 2 ^ (64 - k) := by
    rw [show (2 : Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_div_mul_right _ _ (Nat.two_pow_pos k)]
  have h3 : x.toNat / 2 ^ (64 - k) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 128), Nat.mod_eq_of_lt hb, h1, h2,
    Nat.mod_eq_of_lt h3]

/-! ## Bit masks -/

theorem bitMask_eq (x : BitVec 16) {b : Nat} (hb : b < 8) :
    BitVec.sshiftRight (x.setWidth 64 <<< (63 - b)) 63 =
      0#64 - ((x.setWidth 64 % 256#64) >>> b &&& 1#64) := by
  have ht : x.getLsbD b = decide (x.toNat / 2 ^ b % 2 = 1) := by
    rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  have hy : (x.setWidth 64 % 256#64) >>> b &&& 1#64 = if x.getLsbD b then 1#64 else 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_umod, BitVec.toNat_setWidth,
      Nat.shiftRight_eq_div_pow]
    have h1 : (1#64).toNat = 2 ^ 1 - 1 := rfl
    have h256 : (256#64).toNat = 256 := rfl
    rw [h1, Nat.and_two_pow_sub_one_eq_mod, h256]
    have hx := x.isLt
    rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64)]
    have e : x.toNat % 256 / 2 ^ b % 2 ^ 1 = x.toNat / 2 ^ b % 2 := by
      have : (256 : Nat) = 2 ^ b * 2 ^ (8 - b) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      rw [this, Nat.mod_mul_right_div_self, Nat.pow_one]
      have h2 : 2 ∣ 2 ^ (8 - b) := dvd_pow_self 2 (by omega)
      exact Nat.mod_mod_of_dvd _ h2
    rw [e, ht]
    split
    · rename_i h; simp only [decide_eq_true_eq] at h; rw [h]; rfl
    · rename_i h; simp only [decide_eq_true_eq] at h; rw [show x.toNat / 2 ^ b % 2 = 0 by omega]; rfl
  have hbit : (x.setWidth 64 <<< (63 - b)).getLsbD 63 = x.getLsbD b := by
    simp [show 63 - (63 - b) = b by omega, show ¬ 63 < 63 - b by omega]
  have hmsb : (x.setWidth 64 <<< (63 - b)).msb = x.getLsbD b := by
    rw [BitVec.msb_eq_getLsbD_last]; exact hbit
  have hall : (0#64 - 1#64 : Word) = BitVec.allOnes 64 := by decide
  rw [hy]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  have hl : (if 63 + i < 64 then (x.setWidth 64 <<< (63 - b)).getLsbD (63 + i)
      else (x.setWidth 64 <<< (63 - b)).msb) = x.getLsbD b := by
    by_cases h0 : i = 0
    · subst h0; simpa using hbit
    · simp only [show ¬ (63 + i < 64) by omega, ↓reduceIte, hmsb]
  simp only [show ¬ (64 ≤ i) by omega, decide_false, Bool.not_false, Bool.true_and, hl]
  split
  · rename_i h; rw [hall, BitVec.getLsbD_allOnes, h]; simp [hi]
  · rename_i h; simp [h]

/-- The byte of a bucket below `2048`, times eight: `(x >>> 5) &&& 56`. -/
theorem bucketByte (x : Word) (h : x.toNat < 2048) :
    ((x >>> 5) &&& 56).toNat = 8 * (x.toNat / 256) := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h56 : (56 : Word).toNat = 56 := rfl
  rw [h56]
  have hv : x.toNat / 2 ^ 5 / 8 < 8 := by omega
  have e : x.toNat / 2 ^ 5 = 8 * (x.toNat / 256) + x.toNat / 2 ^ 5 % 8 := by omega
  rw [e]
  generalize x.toNat / 2 ^ 5 % 8 = r at *
  have hr : r < 8 := by omega
  generalize hq : x.toNat / 256 = q at *
  have hq8 : q < 8 := by omega
  interval_cases q <;> interval_cases r <;> rfl

/-- `k - 64` is negative for `k < 64`: its sign spread is all ones. -/
theorem sshift_neg (k : Nat) (hk : k < 64) :
    BitVec.sshiftRight (BitVec.ofNat 64 k - 64) 63 = 0xffffffffffffffff := by
  have hmsb : (BitVec.ofNat 64 k - 64).msb = true := by
    rw [BitVec.msb_eq_toNat, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have : (64 : Word).toNat = 64 := rfl
    rw [this]
    simp only [decide_eq_true_eq]
    omega
  have h63 : (BitVec.ofNat 64 k - 64).getLsbD 63 = true := by
    rw [BitVec.msb_eq_getLsbD_last] at hmsb; exact hmsb
  have e : (0xffffffffffffffff : Word) = BitVec.allOnes 64 := by decide
  rw [e]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_allOnes]
  simp only [show ¬ (64 ≤ i) by omega, decide_false, Bool.not_false, Bool.true_and, hi,
    decide_true]
  by_cases h0 : i = 0
  · subst h0; simpa using h63
  · simp only [show ¬ (63 + i < 64) by omega, ↓reduceIte, hmsb]

theorem slt_neg (k : Nat) (hk : k < 64) : (BitVec.ofNat 64 k - 64).slt 0 = true := by
  rw [show (0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_toNat, BitVec.toNat_sub,
    BitVec.toNat_ofNat]
  have : (64 : Word).toNat = 64 := rfl
  rw [this]
  simp only [decide_eq_true_eq]
  omega

theorem notK_mod (k : Nat) (hk : k < 64) :
    ((BitVec.ofNat 64 k ^^^ 0xffffffffffffffff).toNat % 64) = 63 - k := by
  have : (BitVec.ofNat 64 k ^^^ 0xffffffffffffffff : Word) = BitVec.ofNat 64 (2 ^ 64 - 1 - k) := by
    apply BitVec.eq_of_toNat_eq
    have e : (0xffffffffffffffff : Word) = BitVec.allOnes 64 := by decide
    rw [e, BitVec.xor_allOnes, BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [this, BitVec.toNat_ofNat]
  omega

/-! ## Halfword loads -/

/-- `LHU rd, off(rs1)`: `rd` gets the halfword at the address. -/
theorem step_lhu {code : Code} {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hf : code.fetch s.pc = some (.base (.LHU rd rs1 off)))
    (hv : Sym.validAccess 2 (s.getReg rs1 + signExtend12 off) = true) :
    ∃ t, Steps code 1 s t ∧ t.pc = s.pc + 4 ∧
      (∀ r, t.getReg r = if r = rd ∧ rd ≠ .x0 then
        (s.getHalfword (s.getReg rs1 + signExtend12 off)).zeroExtend 64 else s.getReg r) ∧
      ∀ a, t.getMem a = s.getMem a := by
  obtain ⟨u, hu, hpc, hr, hm⟩ := step_micro (m := .load .hu rd rs1 (signExtend12 off)) hf rfl
    (by simp only [Sym.Micro.exec, Sym.LoadKind.width, hv, ↓reduceIte]; rfl)
  refine ⟨u, hu, hpc, fun r ↦ ?_, fun a ↦ by rw [hm]; simp⟩
  rw [hr]
  show (s.setReg rd _).getReg r = _
  by_cases h : r = rd ∧ rd ≠ .x0
  · obtain ⟨rfl, h0⟩ := h
    rw [MachineState.getReg_setReg_eq h0]
    simp only [true_and, ne_eq, h0, not_false_eq_true, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    by_cases h0 : rd = .x0
    · subst h0; rfl
    · exact MachineState.getReg_setReg_ne _ _ _ _ fun h' ↦ h ⟨h'.symm, h0⟩

/-- A halfword is its two bytes. -/
theorem getHalfword_eq_of_bytes {s t : MachineState} {a : Word} (ha : a.toNat % 2 = 0)
    (h0 : byteAt t a = byteAt s a) (h1 : byteAt t (a + 1) = byteAt s (a + 1)) :
    t.getHalfword a = s.getHalfword a := by
  have hb (u : MachineState) (j : Nat) (hj : j < 16) :
      (u.getHalfword a).getLsbD j = (byteAt u (a + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
    have hp : a.toNat % 8 + j / 8 < 8 := by omega
    have hal : (a + BitVec.ofNat 64 (j / 8)) &&& ~~~7#64 = a &&& ~~~7#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_alignDown, toNat_alignDown, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := a.isLt
      by_cases hw : a.toNat + j / 8 < 2 ^ 64
      · rw [Nat.mod_eq_of_lt (by omega : j / 8 < 2 ^ 64), Nat.mod_eq_of_lt hw]; omega
      · omega
    have hoff : ((a + BitVec.ofNat 64 (j / 8)).toNat % 8) = a.toNat % 8 + j / 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := a.isLt
      rw [Nat.mod_eq_of_lt (by omega : j / 8 < 2 ^ 64)]
      omega
    rw [byteAt_eq, hal, hoff]
    simp only [MachineState.getHalfword, extractHalfword, extractByte, alignToDword, byteOffset,
      toNat_and7, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp only [hj, decide_true, Bool.true_and, show j % 8 < 8 from Nat.mod_lt _ (by decide)]
    congr 1
    omega
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [hb t j hj, hb s j hj]
  have : j / 8 = 0 ∨ j / 8 = 1 := by omega
  rcases this with h | h <;> rw [h]
  · simp only [BitVec.add_zero]; rw [h0]
  · rw [show BitVec.ofNat 64 1 = 1 from rfl, h1]

end Rv64Verifier.Proofs.Bytecode
