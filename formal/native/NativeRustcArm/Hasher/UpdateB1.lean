module

public import NativeRustcArm.Hasher.UpdateInv

/-!
# `Hasher::update`'s loop: the end of a turn

`.LUpdate_1` (`b1`) counts the bytes a turn took (X22) off the remaining ones (X19) and on the
input pointer (X21), then leaves the loop (`.LUpdate_6`) when none remain, else goes back to the
loop head `.LUpdate_2`, which follows it (`b1_spec`).
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Update NativeRustcArm

public section

theorem sub_ofNat_ofNat {n c t : Nat} (h : t ≤ n - c) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - c) - BitVec.ofNat 64 t = BitVec.ofNat 64 (n - (c + t)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0#64) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h
    subst h
    rfl

variable [Host] {k : Nat}

/-- **The end of a turn**: back to the loop head with `c + t` bytes absorbed if input remains,
else to the loop's exit with all of it. -/
theorem b1_spec (hp : Placed code k) {m0 m1 m : MachineData} {c t : Nat}
    (hmid : Mid m0 m1 c t m) :
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Host.addrOf (k + NativeRustcArm.Common.Update.b2Offset) ∧ Inv m0 m1 (c + t) st.data ∧ 0 < t) ∨
        (st.pc = Host.addrOf (k + NativeRustcArm.Common.Update.b8Offset) ∧ Inv m0 m1 (nOf m0) st.data))
      ⟨m, Host.addrOf (k + NativeRustcArm.Common.Update.b1Offset)⟩ := by
  have hwf : (Env.ofMachine m []).WF := Env.wf_of trivial List.Pairwise.nil
  have hm : Match (Env.ofMachine m []) regsS m :=
    match_ofMachine trivial rfl trivial trivial trivial trivial
  refine exec_then (hb1 hp) run_b1 hwf hm fun st hm' hpc => ?_
  have hmem : ∀ p, st.data.dmem.get? p = m.dmem.get? p := fun p =>
    hm'.get?_mem0 hwf fun ⟨_, hw, _⟩ => by simp at hw
  have hn : nOf m0 < 2 ^ 64 := UInt64.toNat_lt _
  have hx19 := hm'.regs .X19 _ rfl
  have hx21 := hm'.regs .X21 _ rfl
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, hmid.x19, hmid.x21,
    hmid.x22] at hx19 hx21
  rw [sub_ofNat_ofNat (by have := hmid.le; omega) hn] at hx19
  rw [add_ofNat_add] at hx21
  have hfr : Frame m0 m1 st.data := hmid.frame.congr
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_atom hm' rfl)
    (UInt64.toBitVec_inj.mp hm'.sp) hmem
  have hH : hasher m0 st.data = hasher m0 m := hasher_congr hmem
  have hx0 : (st.data.regs.getXReg .X0).toNat = bufLen (hasher m0 st.data) := by
    rw [Match.reg_atom hm' rfl, hH]
    exact hmid.x0
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs, hmid.x19, hmid.x22, Nat.add_assoc, NativeRustcArm.Common.Update.b1_next] at hpc
  rw [sub_ofNat_ofNat (by have := hmid.le; omega) hn, ofNat_beq_zero (by omega)] at hpc
  refine Eventually.done _ ?_
  by_cases hend : c + t = nOf m0
  · right
    rw [ite_pos' (by simp; omega), lbl_6 hp] at hpc
    refine ⟨hpc, hfr, le_rfl, ?_, ?_, hx0, ?_⟩
    · rw [hx19, hend, Nat.sub_self]
    · rw [hx21, hend]
    · rw [hH, ← hend]
      exact hmid.holds
  · left
    rw [ite_neg' (by simp; have := hmid.le; omega)] at hpc
    refine ⟨hpc, ⟨hfr, hmid.le, hx19, hx21, hx0, by rw [hH]; exact hmid.holds⟩, ?_⟩
    rcases hmid.pos with h | h
    · exact h
    · omega

end

end NativeRustcArm.Hasher.Update
