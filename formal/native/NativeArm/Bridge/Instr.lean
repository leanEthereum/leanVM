module

public import NativeArm.Bridge.Addr

/-!
# The instruction bridge

Each QM instruction's code, run from a machine that holds the state, ends in a machine that holds
the state `QInstr.step` gives, with every reserved register and SP unchanged
(`QInstr.toArm_correct`).
-/

open Native

namespace NativeArm

public section

/-! ## Values -/

theorem toInt_ofNat_small (n : Nat) (h : n < 64) : (Int64.ofNat n).toInt.toNat = n := by
  rw [Int64.toInt_ofNat']
  simp only [Int.bmod, Int64.size]
  split <;> omega

theorem rotateRight_rotateLeft (x : BitVec 64) (r : Nat) (hr : r < 64) :
    x.rotateRight ((64 - r) % 64) = x.rotateLeft r := by
  rw [BitVec.rotateLeft_def, BitVec.rotateRight_def]
  by_cases h0 : r = 0
  · subst h0; simp [BitVec.ushiftRight_eq_zero]
  · rw [Nat.mod_eq_of_lt (by omega : 64 - r < 64), Nat.mod_eq_of_lt (by omega : 64 - r < 64),
      Nat.mod_eq_of_lt hr, BitVec.or_comm, show 64 - (64 - r) = r by omega]

theorem shl_val (x : UInt64) (n : Nat) :
    (x <<< n.toUInt64).toBitVec = x.toBitVec <<< (n % 64) := by
  simp [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod]

theorem shr_val (x : UInt64) (n : Nat) :
    (x >>> n.toUInt64).toBitVec = x.toBitVec.ushiftRight (n % 64) := by
  simp [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod]

theorem shlcl_val (x c : UInt64) :
    (x <<< (c &&& 63)).toBitVec = x.toBitVec <<< (c.toNat % 64) := by
  simp only [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq']
  congr 1
  simp [BitVec.toNat_umod]
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- A machine after `addImm`: X5 perhaps changed. -/
theorem StateRel.x5 {s : QState} {m m₁ m₂ : MachineData} (hr : StateRel s m₁) (hk : Keeps m m₁)
    (h : m₂ = m₁ ∨ ∃ x, m₂ = m₁.setX .X5 x) : StateRel s m₂ ∧ Keeps m m₂ := by
  rcases h with rfl | ⟨x, rfl⟩
  · exact ⟨hr, hk⟩
  · exact ⟨hr.setX_scratch rfl x, hk.setX rfl x⟩

/-! ## Instructions -/

variable [Labels]

/-- A QM instruction's code, run from a machine holding `s`, ends in one holding the state
`QInstr.step` gives, the reserved registers and SP unchanged. -/
theorem QInstr.toArm_correct (i : QInstr) {s s' : QState} {m : MachineData}
    (h : i.step s = some s') (hr : StateRel s m) :
    Runs i.toArm m (fun m' => StateRel s' m' ∧ Keeps m m') := by
  have hk := Keeps.refl m
  cases i with
  | mov d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.orr (Runs.nil ⟨hr.setX d (by simp [hr.get]), hk.setX (by simp) _⟩)
  | movi d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    have := Runs.movImm (is := []) (Q := fun m' => StateRel (s.setReg d k.toUInt64) m' ∧ Keeps m m')
      d.toX k.toUInt64 (Runs.nil ⟨hr.setX d rfl, hk.setX (by simp) _⟩)
    rwa [List.append_nil] at this
  | load d ad =>
    simp only [QInstr.step, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact Runs.addr ad hr fun m₁ hr1 hk1 _ he =>
      Runs.ldr (Addr.toArm_check ad m₁) he hr1.2 hv
        (Runs.nil ⟨hr1.setX d rfl, hk1.setX (by simp) _⟩)
  | store ad r =>
    simp only [QInstr.step, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact Runs.addr ad hr fun m₁ hr1 hk1 _ he =>
      Runs.str (Addr.toArm_check ad m₁) he hr1.2 hv
        (Runs.nil ⟨by rw [getRegOrZr_xr, hr1.get]; exact hr1.store hv _, hk1.dmem _⟩)
  | storei ad k =>
    simp only [QInstr.step, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [QInstr.toArm]
    split
    · rename_i hk0
      subst hk0
      exact Runs.addr ad hr fun m₁ hr1 hk1 _ he =>
        Runs.str (Addr.toArm_check ad m₁) he hr1.2 hv (Runs.nil
          ⟨by rw [getRegOrZr_xzr, show (0#64 : BitVec 64) = (0 : Int64).toUInt64.toBitVec from rfl]
              exact hr1.store hv _, hk1.dmem _⟩)
    · rw [List.append_assoc]
      exact Runs.movImm _ _ (Runs.addr ad (hr.setX_scratch rfl _) fun m₁ hr1 hk1 h6 he =>
        Runs.str (Addr.toArm_check ad m₁) he hr1.2 hv (Runs.nil
          ⟨by
              rw [getRegOrZr_xr, h6]
              simp only [setX_regs, getXReg_setXReg, ite_true, UInt64.toBitVec_ofBitVec]
              exact hr1.store hv _,
            ((hk.setX rfl _).trans hk1).dmem _⟩))
  | lea d ad =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.armBase ad hr fun m₁ hr1 hk1 _ h5 hv =>
      Runs.addImm_nil _ _ _ h5 fun m₂ hm₂ =>
        ⟨(hr1.x5 hk1 hm₂).1.setX d hv, (hr1.x5 hk1 hm₂).2.setX (by simp) _⟩
  | add d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.add (Runs.nil ⟨hr.setX d (by simp [hr.get]), hk.setX (by simp) _⟩)
  | addi d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.addImm_nil d.toX d.toX k (by simp) fun m₂ hm₂ =>
      ⟨(hr.x5 hk hm₂).1.setX d (by simp [hr.get, Int64.toBitVec_toUInt64]),
        (hr.x5 hk hm₂).2.setX (by simp) _⟩
  | sub d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.sub (Runs.nil ⟨hr.setX d (by simp [hr.get]), hk.setX (by simp) _⟩)
  | subi d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.addImm_nil d.toX d.toX (-k) (by simp) fun m₂ hm₂ =>
      ⟨(hr.x5 hk hm₂).1.setX d (by
          simp [hr.get, Int64.toBitVec_toUInt64, Int64.toBitVec_neg, BitVec.sub_eq_add_neg]),
        (hr.x5 hk hm₂).2.setX (by simp) _⟩
  | xor d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.eor (Runs.nil ⟨hr.setX d (by simp [hr.get]), hk.setX (by simp) _⟩)
  | xori d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.movImm _ _ (Runs.eor (Runs.nil
      ⟨(hr.setX_scratch rfl _).setX d (by simp [hr.get, Int64.toBitVec_toUInt64]),
        (hk.setX rfl _).setX (by simp) _⟩))
  | and d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.and (Runs.nil ⟨hr.setX d (by simp [hr.get]), hk.setX (by simp) _⟩)
  | andi d k =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.movImm _ _ (Runs.and (Runs.nil
      ⟨(hr.setX_scratch rfl _).setX d (by simp [hr.get, Int64.toBitVec_toUInt64]),
        (hk.setX rfl _).setX (by simp) _⟩))
  | or d r =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.orr (Runs.nil ⟨hr.setX d (by simp [hr.get]), hk.setX (by simp) _⟩)
  | not d =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.orn (Runs.nil ⟨hr.setX d (by simp [hr.get]), hk.setX (by simp) _⟩)
  | neg d =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.sub (Runs.nil ⟨hr.setX d (by simp [hr.get]), hk.setX (by simp) _⟩)
  | shli d n =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    refine Runs.orr (Runs.nil ⟨hr.setX d ?_, hk.setX (by simp) _⟩)
    simp only [sval, sr, ShiftRegExpr.interp, getRegOrZr_xr, getRegOrZr_xzr,
      toInt_ofNat_small _ (Nat.mod_lt n (by decide : 64 > 0)), hr.get, shl_val, BitVec.zero_or]
  | shri d n =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    refine Runs.orr (Runs.nil ⟨hr.setX d ?_, hk.setX (by simp) _⟩)
    simp only [sval, sr, ShiftRegExpr.interp, getRegOrZr_xr, getRegOrZr_xzr,
      toInt_ofNat_small _ (Nat.mod_lt n (by decide : 64 > 0)), hr.get, shr_val, BitVec.zero_or]
  | sari d n =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    refine Runs.orr (Runs.nil ⟨hr.setX d ?_, hk.setX (by simp) _⟩)
    simp only [sval, sr, ShiftRegExpr.interp, getRegOrZr_xr, getRegOrZr_xzr,
      toInt_ofNat_small _ (Nat.mod_lt n (by decide : 64 > 0)), hr.get, BitVec.zero_or]
  | roli d n =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    refine Runs.orr (Runs.nil ⟨hr.setX d ?_, hk.setX (by simp) _⟩)
    simp only [sval, sr, ShiftRegExpr.interp, getRegOrZr_xr, getRegOrZr_xzr,
      toInt_ofNat_small _ (Nat.mod_lt _ (by decide : 64 > 0)), hr.get, BitVec.zero_or,
      rotateRight_rotateLeft _ _ (Nat.mod_lt n (by decide : 64 > 0)),
      BitVec.rotateLeft_mod_eq_rotateLeft]
  | shlcl d =>
    simp only [QInstr.step, Option.some.injEq] at h; subst h
    exact Runs.lslv (Runs.nil ⟨hr.setX d (by rw [hr.get, hr.get, shlcl_val]), hk.setX (by simp) _⟩)

end

end NativeArm
