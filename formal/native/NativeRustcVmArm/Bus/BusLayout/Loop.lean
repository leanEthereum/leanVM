module

public import NativeRustcVmArm.Bus.BusLayout.PushTb

/-!
# `bus_layout`: the placements' loop run

`place_step`: `b14` reads size and offset `j` from the frame, then a framework block's placement
(`push_fw`) or a table block's (`push_tb`), then `b13` (`b13_step`). `place_run`: from the first
turn to `.LBusLayout_17`, every placement pushed (`PEnd`).
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)

public section

variable [Host] {k : Nat}

/-- **A turn of the placements' loop.** -/
theorem place_step (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b14Offset)) (hI : PInv L bl m0 j st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b20Offset) ∧ PEnd L bl m0 st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b14Offset) ∧ PInv L bl m0 (j + 1) st'.data)) st := by
  have hS := hpre.1
  have hF : 1840 ≤ busLayoutStack := by decide
  have hn := pre_n hpre
  have hlt := hI.lt
  -- `b14`: size and offset `j`.
  have hwf := Bus.wf_frame (F := 1840) hS hF hI.fr.kept
  have hm : Match (Env.ofMachine st.data [(fb m0, 1840)]) sP st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Bus.base_aligned hS hF rfl, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]; rw [hI.fr.sp]; simp)
      ⟨by show (st.data.regs.getXReg .X23).toBitVec = _; rw [hI.x23]; rfl,
       by show (st.data.regs.getXReg .X22).toBitVec = _; rw [hI.x22]; rfl, trivial⟩ trivial
      ⟨by
        show (st.data.regs.getXReg .X8).toBitVec.toNat < 54
        rw [UInt64.toNat_toBitVec, hI.x8]; omega, trivial⟩ trivial
  refine exec_at (infix_of b14_in_code (by simp [b14]) hp) run_b14 hwf hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hI.fr hm hm1 hwf rfl rfl rfl (ofBlock_keep (by decide))
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have K1 : Bus.KeepRegs [.X8, .X9, .X10, .X11, .X19, .X20, .X21, .X22, .X23] st.data st1.data :=
    KeepRegs.of_block' hm hm1 rfl
  have hI1 : PInv L bl m0 j st1.data :=
    ⟨hfr1, hI.lt, by rw [hd1]; exact hI.sizes, by rw [hd1]; exact hI.offs,
      by rw [hd1]; exact hI.part, by rw [K1 .X19 (by simp), hI.x19],
      by rw [K1 .X8 (by simp), hI.x8], by rw [K1 .X9 (by simp), hI.x9],
      by rw [K1 .X10 (by simp), hI.x10], by rw [K1 .X11 (by simp), hI.x11],
      by rw [K1 .X20 (by simp), hI.x20], by rw [K1 .X21 (by simp), hI.x21],
      by rw [K1 .X22 (by simp), hI.x22], by rw [K1 .X23 (by simp), hI.x23]⟩
  have h13 : st1.data.regs.getXReg .X13 = ((S L bl m0).getD j 0).toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    rw [hm1.regs .X13 _ rfl]
    show Env.load _ 0 (8 + (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64
      (st.data.regs.getXReg .X8).toBitVec).toNat) 8 = _
    rw [memExt3, UInt64.toNat_toBitVec, hI.x8, show 8 + j * 8 % 2 ^ 64 = 8 + 8 * j by omega]
    exact load_word (hI.sizes j hI.lt)
  have h12 : st1.data.regs.getXReg .X12 = ((O L bl m0).1.getD j 0).toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    rw [hm1.regs .X12 _ rfl]
    show Env.load _ 0 (440 + (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64
      (st.data.regs.getXReg .X8).toBitVec).toNat) 8 = _
    rw [memExt3, UInt64.toNat_toBitVec, hI.x8, show 440 + j * 8 % 2 ^ 64 = 440 + 8 * j by omega]
    exact load_word (hI.offs j hI.lt)
  obtain ⟨hpcT, hpcF⟩ := pc_of_cond hpc1
  have hc : (SBool.not (SBool.cmp .ult .W64 (.reg .X8) (.reg .X20))).eval
      (Env.ofMachine st.data [(fb m0, 1840)]) = !decide (j < nf m0) := by
    show (!(SBool.cmp .ult .W64 (.reg .X8) (.reg .X20)).eval _) = _
    rw [eval_ult_reg, hI.x8, hI.x20]
  by_cases hj : j < nf m0
  · have hpc' := hpcF (by rw [hc]; simp [hj])
    exact Eventually.bind (push_fw hp hpre hpc' hI1 h13 h12 hj) fun st2 ⟨hpc2, hM⟩ ↦
      b13_step hp hpre hpc2 hM
  · have hpc' := hpcT (by rw [hc]; simp [hj])
    rw [lbl_14 hp] at hpc'
    exact Eventually.bind (push_tb hp hpre hpc' hI1 h13 h12 (by omega)) fun st2 ⟨hpc2, hM⟩ ↦
      b13_step hp hpre hpc2 hM

/-- **The placements' loop**, from the first turn to `.LBusLayout_17`. -/
theorem place_run (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b14Offset)) (hI : PInv L bl m0 0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b20Offset) ∧ PEnd L bl m0 st'.data) st :=
  Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b14Offset) ∧
      ∃ j, nf m0 + bl.length - j = n ∧ PInv L bl m0 j st.data)
    (fun n st ⟨hpc, j, hn, hI⟩ ↦ (place_step hp hpre hpc hI).mono fun st' h ↦ by
      rcases h with h | ⟨hpc', hI'⟩
      · exact Or.inl h
      · exact Or.inr ⟨nf m0 + bl.length - (j + 1), by have := hI.lt; omega, hpc', j + 1, rfl,
          hI'⟩)
    ⟨hpc, 0, rfl, hI⟩

end

end NativeRustcVmArm.Bus.BusLayout
