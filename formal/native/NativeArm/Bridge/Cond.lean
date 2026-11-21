module

public import NativeArm.Bridge.Imm

/-!
# The condition bridge

A condition's `SUBS` or `ANDS` (after an immediate's moves into X4) keeps the machine holding the
state and sets the flags so that `Cond.armCC` holds exactly when the condition does
(`Cond.toArm_correct`).
-/

open Native

namespace NativeArm

public section

theorem zf_sub (x y : UInt64) : (x.toBitVec - y.toBitVec == 0#64) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add,
    UInt64.toBitVec_inj]

theorem zf_subi (x : UInt64) (k : Int64) :
    (x.toBitVec - k.toBitVec == 0#64) = (x == k.toUInt64) := by
  have := zf_sub x k.toUInt64
  rwa [Int64.toBitVec_toUInt64] at this

theorem cf_sub (x y : UInt64) :
    (BitVec.unsigned (x.toBitVec - y.toBitVec) == x.toBitVec.unsigned - y.toBitVec.unsigned) =
      decide (y ≤ x) := by
  have hx := x.toNat_lt_size
  have hy := y.toNat_lt_size
  simp only [UInt64.size] at hx hy
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, UInt64.le_iff_toNat_le]
  simp only [BitVec.unsigned, BitVec.toNat_sub, UInt64.toNat_toBitVec]
  by_cases h : y.toNat ≤ x.toNat
  · simp only [h, iff_true]
    rw [show 2 ^ 64 - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [h, iff_false]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem cf_subi (x : UInt64) (k : Int64) :
    (BitVec.unsigned (x.toBitVec - k.toBitVec) == x.toBitVec.unsigned - k.toBitVec.unsigned) =
      decide (k.toUInt64 ≤ x) := by
  have := cf_sub x k.toUInt64
  rwa [Int64.toBitVec_toUInt64] at this

theorem zf_and (x y : UInt64) :
    (x.toBitVec &&& y.toBitVec == 0#64) = ((x &&& y) == 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← UInt64.toBitVec_and,
    ← UInt64.toBitVec_inj]
  rfl

/-- A comparison of words. -/
def relU : Rel → UInt64 → UInt64 → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .ltu, x, y => decide (x < y)
  | .geu, x, y => decide (y ≤ x)

theorem Cond.eval_cmp (rel : Rel) (a : Reg64) (b : Rhs) (s : QState) :
    Cond.eval (.cmp rel a b) s = relU rel (s.reg a) (b.eval s) := by
  cases rel <;> rfl

theorem Cond.eval_test (z : Bool) (a : Reg64) (b : Rhs) (s : QState) :
    Cond.eval (.test z a b) s = (((s.reg a &&& b.eval s) == 0) == z) := rfl

theorem subs_cc (rel : Rel) (a : Reg64) (b : Rhs) (x y : UInt64) :
    (Cond.cmp rel a b).armCC.interp
      (StatusFlags.subs (x.toBitVec - y.toBitVec) x.toBitVec y.toBitVec) = relU rel x y := by
  cases rel <;> simp only [Cond.armCC, CondCode.interp, StatusFlags.subs, StatusFlags.from_result,
    BitVec.zero_eq, zf_sub, cf_sub, relU]
  · simp [bne]
  · rw [Bool.eq_iff_iff]
    simp [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]

theorem ands_cc (z : Bool) (a : Reg64) (b : Rhs) (x y : UInt64) :
    (Cond.test z a b).armCC.interp
      (StatusFlags.from_result (x.toBitVec &&& y.toBitVec) { c := false, v := false }) =
      (((x &&& y) == 0) == z) := by
  cases z <;> simp only [Cond.armCC, CondCode.interp, StatusFlags.from_result, BitVec.zero_eq,
    zf_and] <;> simp

variable [Labels]

/-- A condition's code keeps the machine holding `s`, and leaves flags under which `Cond.armCC`
holds exactly when the condition does. -/
theorem Cond.toArm_correct (c : Cond) {s : QState} {m : MachineData} (hr : StateRel s m) :
    Runs c.toArm m
      (fun m' => StateRel s m' ∧ Keeps m m' ∧ c.armCC.interp m'.status = c.eval s) := by
  have hk := Keeps.refl m
  cases c with
  | cmp rel a b =>
    rw [Cond.eval_cmp]
    cases b with
    | reg b =>
      refine Runs.subs (Runs.nil ⟨hr.status _, hk.status _, ?_⟩)
      simp only [getRegOrZr_xr, sval_sr, hr.get, subs_cc, Rhs.eval]
    | imm k =>
      simp only [Cond.toArm]
      split
      · refine Runs.subsi (Runs.nil ⟨hr.status _, hk.status _, ?_⟩)
        simp only [hr.get, ← Int64.toBitVec_toUInt64, subs_cc, Rhs.eval]
      · refine Runs.movImm _ _ (Runs.subs (Runs.nil
          ⟨(hr.setX_scratch rfl _).status _, (hk.setX rfl _).status _, ?_⟩))
        simp only [getRegOrZr_xr, sval_sr, setX_regs, getXReg_setXReg, toX_ne_X4, ite_true,
          ite_false, UInt64.toBitVec_ofBitVec, hr.get, subs_cc,
          Rhs.eval]
  | test z a b =>
    rw [Cond.eval_test]
    cases b with
    | reg b =>
      refine Runs.ands (Runs.nil ⟨hr.status _, hk.status _, ?_⟩)
      simp only [getRegOrZr_xr, sval_sr, hr.get, ands_cc, Rhs.eval]
    | imm k =>
      refine Runs.movImm _ _ (Runs.ands (Runs.nil
        ⟨(hr.setX_scratch rfl _).status _, (hk.setX rfl _).status _, ?_⟩))
      simp only [getRegOrZr_xr, sval_sr, setX_regs, getXReg_setXReg, toX_ne_X4, ite_true,
        ite_false, UInt64.toBitVec_ofBitVec, hr.get, ands_cc, Rhs.eval]

omit [Labels] in
/-- `B.<cc>` on the inverted code branches exactly when the condition fails. -/
theorem Cond.armCC_invert (c : Cond) (f : StatusFlags) :
    c.armCC.invert.interp f = !c.armCC.interp f := by
  cases c with
  | cmp rel => cases rel <;> simp [Cond.armCC, CondCode.invert]
  | test z => cases z <;> simp [Cond.armCC, CondCode.invert]

end

end NativeArm
