module

public import NativeRustcVmArm.Top.Verify.Basic

/-!
# `verify`: the epilogues

From the frame's body at `.LVerify_5` (`b8`, X0 kept) or `.LVerify_6` (`b9`, X0 zero), the
epilogue restores the entry's callee-saved registers and SP and returns (`exit8`, `exit9`).
-/

namespace NativeRustcVmArm.Top.Verify

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Verify

public section

variable [Host] {k : Nat}

/-- The frame as the epilogue's region. -/
theorem frame_match {m0 st : MachineData} {R : BitVec 64 → Prop}
    (hB : Body m0 832 slots R st) (hs : 832 ≤ m0.regs.SP.toBitVec.toNat)
    (hal : m0.regs.SP.toBitVec.toNat % 16 = 0) (hFm : Mapped st.dmem (frameOf m0) 832) :
    (Env.ofMachine st [(frameOf m0, 832)]).WF ∧
      Match (Env.ofMachine st [(frameOf m0, 832)]) frameS st := by
  have hsl := m0.regs.SP.toBitVec.isLt
  have hF : (frameOf m0).toNat = m0.regs.SP.toBitVec.toNat - 832 := toNat_subAddr hs
  refine ⟨Env.wf_of ⟨⟨hFm, show (frameOf m0).toNat + 832 ≤ 2 ^ 64 by omega⟩, trivial⟩
    (List.pairwise_singleton _ _), match_ofMachine
      ⟨rfl, fun _ ↦ show (frameOf m0).toNat % 16 = 0 by omega, trivial⟩
      (show st.regs.SP.toBitVec = frameOf m0 + BitVec.ofInt 64 0 by rw [hB.sp]; simp [frameOf])
      trivial trivial trivial trivial⟩

/-- **The epilogue at `.LVerify_5`**: X0 kept. -/
theorem exit8 (hp : Placed code k) {m0 : MachineData} {R : BitVec 64 → Prop}
    (hs : 832 ≤ m0.regs.SP.toBitVec.toNat) (hal : m0.regs.SP.toBitVec.toNat % 16 = 0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b8Offset)) (hB : Body m0 832 slots R st.data)
    (hFm : Mapped st.data.dmem (frameOf m0) 832) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      st'.data.regs.X0 = st.data.regs.X0 ∧ SameOutside m0.dmem st'.data.dmem R ∧
      Saved m0 st'.data) st := by
  obtain ⟨hwf, hm⟩ := frame_match hB hs hal hFm
  refine exec_at (hb8 hp) run_b8 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hr := b8_restores
  rw [after_eq run_b8] at hr
  obtain ⟨hsv, hret, hdm⟩ := hB.ret hm' hwf (by simp [slots]) hr.1 hr.2
  refine Eventually.done _ ⟨hpc'.trans hret, UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl),
    fun q hq ↦ by rw [hdm]; exact hB.same q hq, hsv⟩

/-- **The epilogue at `.LVerify_6`**: X0 zero. -/
theorem exit9 (hp : Placed code k) {m0 : MachineData} {R : BitVec 64 → Prop}
    (hs : 832 ≤ m0.regs.SP.toBitVec.toNat) (hal : m0.regs.SP.toBitVec.toNat % 16 = 0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b9Offset)) (hB : Body m0 832 slots R st.data)
    (hFm : Mapped st.data.dmem (frameOf m0) 832) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.regs.X0 = 0 ∧
      SameOutside m0.dmem st'.data.dmem R ∧ Saved m0 st'.data) st := by
  obtain ⟨hwf, hm⟩ := frame_match hB hs hal hFm
  refine exec_at (hb9 hp) run_b9 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hr := b9_restores
  rw [after_eq run_b9] at hr
  obtain ⟨hsv, hret, hdm⟩ := hB.ret hm' hwf (by simp [slots]) hr.1 hr.2
  refine Eventually.done _ ⟨hpc'.trans hret, UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl),
    fun q hq ↦ by rw [hdm]; exact hB.same q hq, hsv⟩

end

end NativeRustcVmArm.Top.Verify
