module

public import NativeRustcVmArm.Code.Vm.ColumnWeight.Names
public import NativeRustcVmArm.Code.Vm.EqEval.Names
public import NativeRustcVmArm.Code.Vm.StackPoint.Names
public import NativeRustcVmArm.Ring.Column.Basic

/-!
# `column_weight`'s contract

The prologue and `stack_point` (`b0`), the branch on its result (`b1`): on `None` the tag `0`
stored and the epilogue (`b4`); on `Some`, `eq_eval` over the stack point (`b2`), the value
stored (`b3`), the tag `1` and the epilogue (`b4`).
-/

namespace NativeRustcVmArm.Ring.Column

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Vm.ColumnWeight NativeRustcVmArm.Whir

public section

variable {m0 : MachineData}

/-- **The end**: from a state of the frame and the block run to the return, the contract. -/
theorem post_of [Labels] (h : ColumnWeightPre m0) {m st : MachineData} {S : SState}
    (hfr : CFr m0 m) (hm : Match (envR m0 m) S st) (hok : exitOk S 1104 slots keep = true)
    (hout : outOnly S = true) {v : Option EW} (hv : OptEWAt st.dmem (oA m0) v)
    (hvv : v = if m0.regs.X4.toNat + (m0.regs.X5.toNat - m0.regs.X1.toNat) ≤ 66 then
        some (StackWeight.eval (.eq (stackPoint (placementArg m0)
          (slice m0 m0.regs.X3 m0.regs.X4) m0.regs.X5.toNat)) (slice m0 m0.regs.X6 m0.regs.X7))
      else none) :
    retOf st = retOf m0 ∧ ColumnWeightPost m0 st := by
  have hwf := envR_wf h hfr
  obtain ⟨hret, hS⟩ := hfr.exit hm hwf hok
  refine ⟨hret, hvv ▸ hv, ?_, hS⟩
  have h2 := outOnly_same hm hwf rfl hout
  intro q hq
  rw [h2 q fun h ↦ hq (.inl h)]
  exact hfr.same q fun h ↦ h.elim (fun h ↦ hq (.inr h)) id

variable [Host] {k : Nat}

/-- **`column_weight`'s contract.** -/
theorem columnWeight_spec (hp : Placed code k)
    (hsp : Spec (Labels.label NativeRustcVmArm.Vm.StackPoint.entryLabel) StackPointPre StackPointPost)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost := by
  intro m0 h
  rw [show Labels.label NativeRustcVmArm.Vm.ColumnWeight.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.ColumnWeight.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.ColumnWeight.entryOffset) NativeRustcVmArm.Vm.ColumnWeight.entry_at]
  refine stepEntry hp h hsp fun m2 hM hres ↦ ?_
  have hwf := envR_wf h hM.fr
  have hm := matchR h hM
  refine exec_then (hb b1_in_code (by simp [b1]) hp) run_b1 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hc : (SBool.not (.cmp .eq .W64 (.reg .X0) (.lit 1))).eval (envR m0 m2) =
      !(m2.regs.X0.toBitVec == BitVec.ofNat 64 1) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Env.ofMachine_regs, low_W64]
    rfl
  by_cases hn : nOf m0 ≤ 66
  · rw [ite_eq_left hn] at hres
    obtain ⟨hx0, hx1, hz⟩ := hres
    simp only [PcOk, hc, hx0] at hpc1
    rw [show (!((1 : UInt64).toBitVec == BitVec.ofNat 64 1)) = false from rfl] at hpc1
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
    rw [show k + NativeRustcVmArm.Vm.ColumnWeight.b1Offset + b1.length = k + NativeRustcVmArm.Vm.ColumnWeight.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ColumnWeight.b1_next]] at hpc1
    refine exec_at (hb b2_in_code (by simp [b2]) hp) run_b2 hwf hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
    have hfr2 : CFr m0 st2.data :=
      hM.fr.ofBlock hm hm2 hwf rfl rfl rfl fun r hr ↦ by
        simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    have hd2 : st2.data.dmem = m2.dmem := hm2.dmem_eq hwf rfl
    have e0 : st2.data.regs.X0.toBitVec = fb m0 := by
      rw [show st2.data.regs.X0 = st2.data.regs.getXReg .X0 from rfl, hm2.regs .X0 (.ptr 0 0) rfl]
      simp [Sym.eval]
    have e1 : st2.data.regs.X1 = m2.regs.X1 := reg_of hm2 (r := .X1) (v := .reg .X1) rfl rfl
    have e2 : st2.data.regs.X2 = m0.regs.X6 :=
      reg_of hm2 (r := .X2) (v := .reg .X21) rfl (by simp [Sym.eval, hM.x21])
    have e3 : st2.data.regs.X3 = m0.regs.X7 :=
      reg_of hm2 (r := .X3) (v := .reg .X20) rfl (by simp [Sym.eval, hM.x20])
    have hfw := fbw h
    have hN' := hN h
    rw [stack_eq] at hN'
    have hx := h.2.2.1
    have hpre : EqEvalPre st2.data := by
      simp only [EqEvalPre, SliceOk, Readable, OffStack, e0, e1, e2, e3, hx1]
      refine ⟨hfr2.stackOk h.1 (by decide) (by decide), ⟨⟨fun j hj ↦ hfr2.kept _
        (frame_mapped h.1 (by decide) j (by unfold nOf at *; omega)), by
          unfold NoWrap at *; unfold nOf at *; omega⟩, ?_⟩,
        ⟨⟨fun j hj ↦ hfr2.kept _ (hx.1.1 j hj), hx.1.2⟩, hfr2.apart (hN h) hx.2 (by decide)⟩⟩
      have := apart_callee h hfr2 (o := 0) (n := 16 * nOf m0) (N' := eqEvalStack)
        (by unfold nOf at *; omega) (by decide)
      rwa [NativeRustcVm.addr_add_zero] at this
    have hnil : ∀ q, ¬InRange (0 : BitVec 64) 0 q := fun q hq ↦ by unfold InRange at hq; omega
    refine Fr.leafAt hfr2 (hN h) (N' := eqEvalStack) (by decide) keep_cs slots_le
      (fun _ h ↦ h.elim) hee hpc2 hpre
      (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ hq.elim
        (fun hq ↦ absurd hq (hnil q)) .inl, hq.2.2⟩)
      fun m3 hfr3 hq hcs ↦ ?_
    rw [show k + NativeRustcVmArm.Vm.ColumnWeight.b2Offset + b2.length = k + NativeRustcVmArm.Vm.ColumnWeight.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ColumnWeight.b2_next]]
    have hM3 : Mid m0 m3 :=
      ⟨hfr3, (hcs .X19 rfl).trans ((Match.reg_eq hm hm2 (r := .X19) rfl rfl).trans hM.x19),
        (hcs .X20 rfl).trans ((Match.reg_eq hm hm2 (r := .X20) rfl rfl).trans hM.x20),
        (hcs .X21 rfl).trans ((Match.reg_eq hm hm2 (r := .X21) rfl rfl).trans hM.x21)⟩
    have hval : (⟨m3.regs.getXReg .X0, m3.regs.getXReg .X1⟩ : EW) =
        StackWeight.eval (.eq (zOf m0)) (slice m0 m0.regs.X6 m0.regs.X7) := by
      show ewRet m3 = _
      rw [hq.1]
      have hzs : slice st2.data st2.data.regs.X0 st2.data.regs.X1 = zOf m0 := by
        unfold slice
        rw [e0, e1, hx1, hd2, ← zOf_size, ← Array.length_toList,
          NativeRustcVm.ewsOf_of_ewsAt hz]
      have hxs : slice st2.data st2.data.regs.X2 st2.data.regs.X3 =
          slice m0 m0.regs.X6 m0.regs.X7 := by
        unfold slice
        rw [e2, e3, NativeRustcVm.ewsOf_congr fun j hj ↦ same_of h hfr2 hx.2 hx.1.2 hj]
      rw [hzs, hxs]
      rfl
    have hwf3 := envR_wf h hfr3
    have hm3 := matchR h hM3
    refine exec_then (hb b3_in_code (by simp [b3]) hp) run_b3 hwf3 hm3 fun st4 hm4 hpc4 ↦ ?_
    simp only [PcOk] at hpc4
    rw [show k + NativeRustcVmArm.Vm.ColumnWeight.b3Offset + b3.length = k + NativeRustcVmArm.Vm.ColumnWeight.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ColumnWeight.b3_next]] at hpc4
    refine exec_at (hb b4_in_code (by simp [b4]) hp) run_b4s hwf3 hpc4 hm4 fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨hret, hpost⟩ := post_of h hfr3 hm5 (by decide) (by decide)
      (outSome_at hm5 rfl (by decide)) (by rw [ite_eq_left (show m0.regs.X4.toNat + (m0.regs.X5.toNat - m0.regs.X1.toNat) ≤ 66 from hn), hval]; rfl)
    exact .done _ ⟨by simp only [PcOk] at hpc5; rw [hpc5, hret], hpost⟩
  · rw [ite_eq_right hn] at hres
    simp only [PcOk, hc, hres] at hpc1
    rw [show (!((0 : UInt64).toBitVec == BitVec.ofNat 64 1)) = true from rfl] at hpc1
    simp only [↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.ColumnWeight.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.ColumnWeight.b4Offset) from
      hp.label (j := NativeRustcVmArm.Vm.ColumnWeight.b4Offset) NativeRustcVmArm.Vm.ColumnWeight.label_2_at] at hpc1
    refine exec_at (hb b4_in_code (by simp [b4]) hp) run_b4n hwf hpc1 hm1 fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨hret, hpost⟩ := post_of h hM.fr hm5 (by decide) (by decide)
      (outNone_at hm5 rfl (by decide)) (by rw [ite_eq_right (show ¬ m0.regs.X4.toNat + (m0.regs.X5.toNat - m0.regs.X1.toNat) ≤ 66 from hn)])
    exact .done _ ⟨by simp only [PcOk] at hpc5; rw [hpc5, hret], hpost⟩

end

end NativeRustcVmArm.Ring.Column
