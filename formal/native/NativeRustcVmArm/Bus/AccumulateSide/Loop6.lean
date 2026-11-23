module

public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Bus.AccumulateSide.Padding

/-!
# `accumulate_side`: evaluating the block form on its owner's padding row
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-- **`b35`**: the block form evaluated at the owner's padding row. -/
theorem turn35 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L35 m)
    (hg : FormBufAt m.dmem (base m0 F + BitVec.ofNat 64 152) (gf m0 (BA L rows bl) j))
    {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L36 m2 →
      FormBufAt m2.dmem (base m0 F + BitVec.ofNat 64 152) (gf m0 (BA L rows bl) j) → KeepF m0 m m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b36Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b35Offset)⟩ := by
  have hH0 := St.lift (D := L35) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  have hsz := hg.len_le
  change (gf m0 (BA L rows bl) j).size ≤ 148 at hsz
  have hol : (blk (BA L rows bl) j).owner < 6 := by
    rw [blk_eq hj]
    exact (h.bown bl[j] (List.getElem_mem hj)).1
  refine St.runCallK h (.inl rfl) (sz := [12096]) rfl
    (b35_in_code.trans hp.1 (by simp [b35])) run_b35 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := L34c) (E := [(.reg .X23, 108), (.reg .X24, 109)]) (by decide) (by decide)
    (fun st hm' p hp' ↦ ?_) (N' := evaluateStack) le_ev (by decide) (hev (gf m0 (BA L rows bl) j))
    (fun st hm' hst' ↦ ?_) (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1
      (fun _ h ↦ h.elim (fun h ↦ by unfold InRange at h; omega) id), hq.2.2⟩)
    fun st m2 hm' hst' hst2 hq hF hB ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact argv (sz := [12096]) rfl hH0 hm' (r := .X23) (a := 108) (by decide)
    · exact argv (sz := [12096]) rfl hH0 hm' (r := .X24) (a := 109) (by decide)
  all_goals
    have e0 : st.regs.X0.toBitVec = base m0 F + BitVec.ofNat 64 160 := by
      change (st.regs.getXReg .X0).toBitVec = _
      rw [argv (sz := [12096]) rfl hH0 hm' (a := 23) (by decide)]
      rfl
    have e1 : st.regs.X1.toNat = (gf m0 (BA L rows bl) j).size := by
      change (st.regs.getXReg .X1).toNat = _
      rw [argv (sz := [12096]) rfl hH0 hm' (a := 101) (by decide)]
      change (gf m0 (BA L rows bl) j).size.toUInt64.toNat = _
      exact UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
    have e2 : st.regs.X2.toBitVec = NativeRustcVmArm.rodataAddr .padding + BitVec.ofNat 64 (16 *
        (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * (blk (BA L rows bl) j).owner + 3) 0).toNat) := by
      change (st.regs.getXReg .X2).toBitVec = _
      rw [argv (sz := [12096]) rfl hH0 hm' (a := 104) (by decide)]
      rfl
    have e3 : st.regs.X3.toNat =
        (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * (blk (BA L rows bl) j).owner + 4) 0).toNat := by
      change (st.regs.getXReg .X3).toNat = _
      rw [argv (sz := [12096]) rfl hH0 hm' (a := 102) (by decide)]
      rfl
    have hro := Bus.Fr.rodataAt hst'.fr h.rodata h.stack.2.1 le_ev
      (fun t i hi ho ↦ rodataApart_out h.formsRo h.rodata h.formsOk.1.2 t i hi ho)
    have hpad := padding_slice hro hol e2 e3
  · have hg' := fb_block (F_le h) hm' hwf (by decide) hg
    have ht := Bus.local_ok h.stack le_ev (o := 160) (n := termBytes * (gf m0 (BA L rows bl) j).size)
      (by unfold termBytes F; omega) hst'.fr.kept hst'.fr.sp
    refine ⟨hst'.fr.stackOk h.stack (by decide) le_ev, e1, ?_, ?_, ?_, hpad.1⟩
    · rw [e0]
      simpa only [NativeRustcVm.addr_add_add] using hg'.terms
    · rw [e0, e1]
      exact ht.1
    · rw [e0, e1]
      exact ht.2
  · have hr : ewRet m2 = ev m0 (BA L rows bl) j := by
      rw [hq.1, hpad.2]
    rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b35Offset + b35.length = k + NativeRustcVmArm.Vm.AccumulateSide.b36Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b35_next]]
    exact cont m2 ⟨hst2.fr, holds_ewRet (r0 := 110) (Holds.sub hst2.hd
      (D' := (Sym.reg .X23, 108) :: (Sym.reg .X24, 109) :: L34c) (by decide)) hr rfl rfl⟩
      (NativeRustcVm.Tables.FormBufAt.of_same hg (hB 152 5928 (by decide) (by decide))) hF

end

end NativeRustcVmArm.Bus.AccumulateSide
