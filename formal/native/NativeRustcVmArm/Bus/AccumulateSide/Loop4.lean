module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Bus.AccumulateSide.Loop3

/-!
# `accumulate_side`: the table loop's products

`b34` multiplies the selector by the padding weight. `b36` multiplies that result by the padding row's form value plus one. Both calls preserve the forms and the frame's `FormBuf`.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-- **`b34`**: selector times padding weight. -/
theorem turn34 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L34 m) {g : FormW}
    (hg : FormBufAt m.dmem (base m0 F + BitVec.ofNat 64 152) g) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L35 m2 →
      FormBufAt m2.dmem (base m0 F + BitVec.ofNat 64 152) g → KeepF m0 m m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b35Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b34Offset)⟩ := by
  have hH0 := St.lift (D := L34) hst (by decide) 0 []
  refine St.mulCall h hmul (.inl rfl) (sz := [12096]) rfl
    (b34_in_code.trans hp.1 (by simp [b34])) run_b34 hst.fr hH0 (wf0 h hst.fr.kept)
    (matchF h hst.fr.sp) rfl (by decide) (D' := L34c) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) (by decide) fun st m2 hm' hst2 hret hF hB ↦ ?_
  change ewRet m2 = EW.mul ⟨st.regs.getXReg .X0, st.regs.getXReg .X1⟩
    ⟨st.regs.getXReg .X2, st.regs.getXReg .X3⟩ at hret
  rw [argv (sz := [12096]) rfl hH0 hm' (r := .X0) (a := 94) (by decide),
    argv (sz := [12096]) rfl hH0 hm' (r := .X1) (a := 95) (by decide),
    argv (sz := [12096]) rfl hH0 hm' (r := .X2) (a := 106) (by decide),
    argv (sz := [12096]) rfl hH0 hm' (r := .X3) (a := 107) (by decide)] at hret
  change ewRet m2 = sp1 SL m0 (BA L rows bl) j at hret
  rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b34Offset + b34.length = k + NativeRustcVmArm.Vm.AccumulateSide.b35Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b34_next]]
  exact cont m2 ⟨hst2.fr, holds_ewRet (Holds.sub hst2.hd (D' := L34c) (by decide)) hret rfl rfl⟩
    (NativeRustcVm.Tables.FormBufAt.of_same hg (hB 152 5928 (by decide) (by decide))) hF

/-- **`b36`**: the padding row's term. -/
theorem turn36 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L36 m) {g : FormW}
    (hg : FormBufAt m.dmem (base m0 F + BitVec.ofNat 64 152) g) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L37 m2 →
      FormBufAt m2.dmem (base m0 F + BitVec.ofNat 64 152) g → KeepF m0 m m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b37Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b36Offset)⟩ := by
  have hH0 := St.lift (D := L36) hst (by decide) 0 []
  refine St.mulCall h hmul (.inl rfl) (sz := [12096]) rfl
    (b36_in_code.trans hp.1 (by simp [b36])) run_b36 hst.fr hH0 (wf0 h hst.fr.kept)
    (matchF h hst.fr.sp) rfl (by decide) (D' := L34c) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) (by decide) fun st m2 hm' hst2 hret hF hB ↦ ?_
  have hx2 : st.regs.getXReg .X2 = (ev m0 (BA L rows bl) j).c0 ^^^ 1 := by
    change tval [(base m0 F, F + 0)] st (.reg .X2) = _
    rw [tval_reg_of hm' rfl, ofBitVec_eor]
    change m.regs.getXReg .X0 ^^^ 1 = _
    rw [Holds.regv hst.hd (r := .X0) (i := 110) (by decide)]
    rfl
  change ewRet m2 = EW.mul ⟨st.regs.getXReg .X0, st.regs.getXReg .X1⟩
    ⟨st.regs.getXReg .X2, st.regs.getXReg .X3⟩ at hret
  rw [argv (sz := [12096]) rfl hH0 hm' (r := .X0) (a := 108) (by decide),
    argv (sz := [12096]) rfl hH0 hm' (r := .X1) (a := 109) (by decide), hx2,
    argv (sz := [12096]) rfl hH0 hm' (r := .X3) (a := 111) (by decide)] at hret
  have hr : ewRet m2 = pterm SL m0 (BA L rows bl) j := by
    change ewRet m2 = EW.mul (sp1 SL m0 (BA L rows bl) j)
      ⟨(ev m0 (BA L rows bl) j).c0 ^^^ 1, (ev m0 (BA L rows bl) j).c1 ^^^ 0⟩
    rw [UInt64.xor_zero]
    exact hret
  rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b36Offset + b36.length = k + NativeRustcVmArm.Vm.AccumulateSide.b37Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b36_next]]
  exact cont m2 ⟨hst2.fr, holds_ewRet (Holds.sub hst2.hd (D' := L34c) (by decide)) hr rfl rfl⟩
    (NativeRustcVm.Tables.FormBufAt.of_same hg (hB 152 5928 (by decide) (by decide))) hF

end

end NativeRustcVmArm.Bus.AccumulateSide
