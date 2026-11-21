module

public import NativeArm.Bridge.Run

/-!
# Immediates

`movImm t k` leaves `k` in `t` and changes no other register (`Runs.movImm`): each chunk of 16 bits
is the one `MOVZ` or `MOVN` set, or the one a later `MOVK` set (`Chunk`); `addImm d b k` leaves
`b + k` in `d`, through X5 when `k` is no 12-bit immediate (`Runs.addImm`).
-/

open Native

namespace NativeArm

@[expose] public section

/-- `v` holds `k`'s bits `16 * j` to `16 * j + 15`. -/
def Chunk (v : BitVec 64) (k : UInt64) (j : Nat) : Prop :=
  ∀ i < 16, v.getLsbD (16 * j + i) = k.toBitVec.getLsbD (16 * j + i)

end

public section

/-! ## Bits -/

theorem testBit_chunk (k : UInt64) (j i : Nat) :
    (chunk k j).testBit i = (decide (i < 16) && k.toBitVec.getLsbD (16 * j + i)) := by
  simp only [chunk, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, BitVec.getLsbD,
    UInt64.toNat_toBitVec]
  rw [Nat.add_comm]

theorem chunk_lt (k : UInt64) (j : Nat) : chunk k j < 2 ^ 16 := Nat.mod_lt _ (by decide)

theorem getLsbD_ffff (i : Nat) : (0xFFFF#64).getLsbD i = decide (i < 16) := by
  rw [BitVec.getLsbD_ofNat, show (0xFFFF : Nat) = 2 ^ 16 - 1 from rfl,
    Nat.testBit_two_pow_sub_one]
  by_cases h : i < 16
  · simp [h, show i < 64 by omega]
  · simp [h]

theorem testBit_ffff (i : Nat) : Nat.testBit 65535 i = decide (i < 16) := by
  rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem imm16 (c : Nat) (hc : c < 2 ^ 16) :
    BitVec.ofInt 64 (Int64.ofNat c).toInt &&& 0xFFFF#64 = BitVec.ofNat 64 c := by
  rw [ofInt_toInt64, Int64.toBitVec_ofNat']
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, getLsbD_ffff, BitVec.getLsbD_ofNat]
  by_cases h : i < 16
  · simp [h]
  · simp only [h, decide_false, Bool.and_false, hi, decide_true, Bool.true_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide)
      (by omega)))).symm

/-- `MOVK`'s result. -/
abbrev movkv (v : BitVec 64) (c : Nat) (s : Nat) : BitVec 64 :=
  (v &&& ~~~(0xFFFF#64 <<< s)) ||| ((BitVec.ofInt 64 (Int64.ofNat c).toInt &&& 0xFFFF#64) <<< s)

theorem getLsbD_movkv (v : BitVec 64) (c : Nat) (hc : c < 2 ^ 16) (s p : Nat) (hp : p < 64) :
    (movkv v c s).getLsbD p =
      if s ≤ p ∧ p < s + 16 then c.testBit (p - s) else v.getLsbD p := by
  simp only [movkv, imm16 c hc, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, testBit_ffff, hp, decide_true, Bool.true_and]
  by_cases h1 : s ≤ p
  · by_cases h2 : p < s + 16
    · simp [h1, h2, show ¬ p < s by omega, show p - s < 16 by omega, show p - s < 64 by omega]
    · have : c.testBit (p - s) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide)
          (by omega)))
      simp [h1, h2, this, show ¬ p < s by omega, show ¬ p - s < 16 by omega]
  · simp [h1, show p < s by omega]

theorem Chunk.movk_same (v : BitVec 64) (k : UInt64) {j : Nat} (hj : j < 4) :
    Chunk (movkv v (chunk k j) (16 * j)) k j := by
  intro i hi
  have hin : 16 * j ≤ 16 * j + i ∧ 16 * j + i < 16 * j + 16 := by omega
  rw [getLsbD_movkv _ _ (chunk_lt k j) _ _ (by omega), ite_eq_left hin, testBit_chunk,
    show 16 * j + i - 16 * j = i by omega]
  simp [hi]

theorem Chunk.movk_other {v : BitVec 64} {k : UInt64} {j j' : Nat} (h : Chunk v k j')
    (hj' : j' < 4) (hne : j' ≠ j) (c : Nat) (hc : c < 2 ^ 16) :
    Chunk (movkv v c (16 * j)) k j' := by
  intro i hi
  have hout : ¬ (16 * j ≤ 16 * j' + i ∧ 16 * j' + i < 16 * j + 16) := by omega
  rw [getLsbD_movkv _ _ hc _ _ (by omega), ite_eq_right hout]
  exact h i hi

theorem Chunk.eq {v : BitVec 64} {k : UInt64} (h : ∀ j < 4, Chunk v k j) : v = k.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := h (i / 16) (by omega) (i % 16) (by omega)
  rwa [show 16 * (i / 16) + i % 16 = i by omega] at this

/-! ## `movImm` -/

@[simp] theorem setX_setX (m : MachineData) (r : XReg) (a b : BitVec 64) :
    (m.setX r a).setX r b = m.setX r b := by
  cases r <;> rfl

theorem testBit_chunk_eq {k : UInt64} {j c : Nat} (h : chunk k j = c) {i : Nat} (hi : i < 16) :
    k.toBitVec.getLsbD (16 * j + i) = c.testBit i := by
  rw [← h, testBit_chunk]
  simp [hi]


variable [Labels] {is : List Instr} {m : MachineData} {Q : MachineData → Prop}

/-- What a `MOVK` sequence keeps: the chunks below `n` are `k`'s, and so is each one from `n` on
that equals `fill`. -/
def MovInv (v : BitVec 64) (k : UInt64) (fill n : Nat) : Prop :=
  (∀ j < n, Chunk v k j) ∧ ∀ j, n ≤ j → j < 4 → chunk k j = fill → Chunk v k j

theorem Runs.movkIf {t : XReg} {k : UInt64} {fill j : Nat} {s : MovShift .W64}
    (hs : s.toNat = 16 * j) (hj : j < 4) {v : BitVec 64} (hv : MovInv v k fill j)
    (h : ∀ v', MovInv v' k fill (j + 1) → Runs is (m.setX t v') Q) :
    Runs (movkIf t k fill j s ++ is) (m.setX t v) Q := by
  unfold NativeArm.movkIf
  split
  · rename_i hf
    refine h v ⟨fun j' hj' => ?_, fun j' h1 h2 h3 => hv.2 j' (by omega) h2 h3⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
    · exact hv.1 j' hj'
    · exact hv.2 j' (by omega) hj hf
  · refine Runs.movk ?_
    simp only [setX_setX, setX_regs, getXReg_setXReg, ite_true, UInt64.toBitVec_ofBitVec, hs]
    refine h _ ⟨fun j' hj' => ?_, fun j' h1 h2 h3 => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · exact (hv.1 j' hj').movk_other (by omega) (by omega) _ (chunk_lt k j)
      · exact Chunk.movk_same v k hj
    · exact (hv.2 j' (by omega) h2 h3).movk_other h2 (by omega) _ (chunk_lt k j)

theorem Runs.movks {t : XReg} {k : UInt64} {fill : Nat} {v : BitVec 64} (hv : MovInv v k fill 1)
    (h : Runs is (m.setX t k.toBitVec) Q) : Runs (movks t k fill ++ is) (m.setX t v) Q := by
  simp only [NativeArm.movks, List.append_assoc]
  refine Runs.movkIf rfl (by decide) hv fun v₂ h₂ => ?_
  refine Runs.movkIf rfl (by decide) h₂ fun v₃ h₃ => ?_
  refine Runs.movkIf rfl (by decide) h₃ fun v₄ h₄ => ?_
  rw [Chunk.eq fun j hj => h₄.1 j hj]
  exact h

/-- `movImm t k` leaves `k` in `t`. -/
theorem Runs.movImm (t : XReg) (k : UInt64) (h : Runs is (m.setX t k.toBitVec) Q) :
    Runs (NativeArm.movImm t k ++ is) m Q := by
  simp only [NativeArm.movImm]
  split
  · refine Runs.movn ?_
    rw [imm16 _ (chunk_lt _ _)]
    refine Runs.movks ⟨fun j hj => ?_, fun j h1 h2 h3 => ?_⟩ h
    · intro i hi
      obtain rfl : j = 0 := by omega
      rw [BitVec.getLsbD_not, BitVec.getLsbD_ofNat, testBit_chunk]
      simp [hi, show i < 64 by omega]
    · intro i hi
      rw [BitVec.getLsbD_not, BitVec.getLsbD_ofNat, testBit_chunk_eq h3 hi,
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (chunk_lt _ _)
          (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp [show 16 * j + i < 64 by omega, testBit_ffff, hi]
  · refine Runs.movz ?_
    rw [imm16 _ (chunk_lt _ _)]
    refine Runs.movks ⟨fun j hj => ?_, fun j h1 h2 h3 => ?_⟩ h
    · intro i hi
      obtain rfl : j = 0 := by omega
      rw [BitVec.getLsbD_ofNat, testBit_chunk]
      simp [hi, show i < 64 by omega]
    · intro i hi
      rw [BitVec.getLsbD_ofNat, testBit_chunk_eq h3 hi,
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (chunk_lt _ _)
          (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp


omit [Labels] in
@[simp] theorem sval_sr (m : MachineData) (r : XReg) :
    sval m (sr r) = (m.regs.getXReg r).toBitVec := by
  simp [sval, sr, ShiftRegExpr.interp]

/-- `addImm d b k` leaves `b + k` in `d`, perhaps through X5. -/
theorem Runs.addImm (d b : XReg) (k : Int64) (hb : b ≠ .X5)
    (h : ∀ m₁, (m₁ = m ∨ ∃ x, m₁ = m.setX .X5 x) →
      Runs is (m₁.setX d ((m.regs.getXReg b).toBitVec + k.toBitVec)) Q) :
    Runs (NativeArm.addImm d b k ++ is) m Q := by
  unfold NativeArm.addImm
  split
  · exact Runs.addi (h m (Or.inl rfl))
  · split
    · refine Runs.subi ?_
      rw [Int64.toBitVec_neg, BitVec.sub_neg]
      exact h m (Or.inl rfl)
    · rw [List.append_assoc]
      refine Runs.movImm _ _ (Runs.add ?_)
      simp only [setX_regs, getRegOrZr_xr, getXReg_setXReg, hb, ite_false, sval_sr, ite_true,
        UInt64.toBitVec_ofBitVec, Int64.toBitVec_toUInt64]
      exact h _ (Or.inr ⟨_, rfl⟩)

/-- `addImm d b k` alone. -/
theorem Runs.addImm_nil (d b : XReg) (k : Int64) (hb : b ≠ .X5)
    (h : ∀ m₁, (m₁ = m ∨ ∃ x, m₁ = m.setX .X5 x) →
      Q (m₁.setX d ((m.regs.getXReg b).toBitVec + k.toBitVec))) :
    Runs (NativeArm.addImm d b k) m Q := by
  have := Runs.addImm (is := []) d b k hb fun m₁ h₁ => Runs.nil (h m₁ h₁)
  rwa [List.append_nil] at this

end

end NativeArm
