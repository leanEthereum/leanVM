module

public import NativeRustcVmX64.Bus.AccumulateSide.TurnD
public import NativeRustcVmX64.Code.Vm.PaddingWeight.Names

/-! # `accumulate_side`: the padding weight (x86-64) -/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

 theorem turnE (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hpw : Spec (Labels.label NativeRustcVmX64.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost)
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (outs m0) (VT L rows bl Fm SL m0 j) (D23 ++ E23) 8 m)
    (hfb : FB m0 m.dmem (fmA L rows bl m0 j))
    (hG : FormsAt m.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 (j + 1)).1)
    (hsi : reg m .rsi = BitVec.ofNat 64 (bkA L rows bl j).logRows)
    (hdx : reg m .rdx = BitVec.ofNat 64 (bkA L rows bl j).rows)
    {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (outs m0) (VT L rows bl Fm SL m0 j) D23c 8 m2 →
      FB m0 m2.dmem (fmA L rows bl m0 j) →
      FormsAt m2.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 (j + 1)).1 →
      ewRet m2 = pwA L rows bl m0 j →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b24Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b23Offset + b23a.length)⟩ := by
  let env := frameEnv m0 m F [(rspOf m0 + 8#64, 88)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b23Offset + b23a.length + b23b.length)).toBitVec
  have hwf : env.WF := wf1 h hst.fr.kept h.argsIn
  have hh : (bkA L rows bl j).logRows ≤ 30 := by
    change ((BA L rows bl).getD j default).logRows ≤ 30
    rw [BA_getD L rows bl hj]
    show L.tableLogHeights.getD bl[j].owner 0 ≤ 30
    have ho := (h.bown _ (List.getElem_mem hj)).1
    have hi : bl[j].owner < L.tableLogHeights.size := by rw [h.lay.heights_size]; exact ho
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
    exact h.lay.heights_le _ (Array.getElem_mem hi)
  obtain ⟨hmid, hw, htr, hdi, hsi', hdx'⟩ := ok_b23b
  refine St.run h (rest := [(rspOf m0 + 8#64, 88)]) (vs := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b23Offset + b23a.length + b23b.length)).toBitVec) rfl
    (infix_of (F := code) (k := k) (j := NativeRustcVmX64.Vm.AccumulateSide.b23Offset + b23a.length) b23b_in_code (by simp [b23b, b23]) hp) exit_b23b (fun _ _ ↦ rfl) hst.fr hst.same
    ((hst.hd.reg0 (rs' := [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]) (by decide) rfl).append
      (St.holdsDA h hst outs_id)) (by decide) hwf
    (St.mt hst ⟨rfl, rfl, trivial⟩ trivial trivial argAliases_ok) hmid hw (by decide) htr
    fun st hm hpc hst' _ ↦ ?_
  have hk := run_keep hwf hm low_T.2.2.2.2.2.2.2.2.1 (writesIn_of_mid hmid)
  have hfb' := KeepF.fbuf hk hfb
  have hG' := KeepF.forms h hk hG
  have edi : reg st.data .rdi = stackArg m0 7 :=
    (hm.regs .rdi _ hdi).trans (St.arg h hst outs_id (i := 7) (by decide))
  have edx : reg st.data .rdx = BitVec.ofNat 64 (bkA L rows bl j).rows :=
    (hm.regs .rdx _ hdx').trans hdx
  have esi : (reg st.data .rsi).toNat = min (bkA L rows bl j).logRows (stackArg m0 8).toNat := by
    change (st.data.regs.get64 .rsi).toNat = _
    rw [hm.regs .rsi _ hsi']
    change (if (!(CmpOp.apply .ult .W64 (reg m .rsi) (env.load 1 64 8))) = true
      then env.load 1 64 8 else reg m .rsi).toNat = _
    rw [St.arg h hst outs_id (i := 8) (by decide), hsi]
    simp only [CmpOp.apply, low_W64, BitVec.ult, toNat_ofNat_lt (by omega : (bkA L rows bl j).logRows < 2 ^ 64)]
    split <;> rename_i hc
    · rw [Nat.min_eq_right]; simpa using hc
    · rw [toNat_ofNat_lt (by omega), Nat.min_eq_left]
      exact Nat.le_of_lt (by simpa using hc)
  have hs : rspOf st.data = fb m0 := by rw [hst'.fr.sp, off_zero]
  have hn : (reg st.data .rsi).toNat ≤ (stackArg m0 8).toNat := by rw [esi]; exact Nat.min_le_right _ _
  have hpre : PaddingWeightPre st.data := by
    refine ⟨St.stackOk h hst' le_pw, by have := h.pn; omega, ?_⟩
    rw [edi]
    exact sliceOk_prefix (St.sliceOk h hst' le_pw h.pt) hn
  have hpoint : slice st.data (reg st.data .rdi) (reg st.data .rsi) =
      (ptA m0).extract 0 (bkA L rows bl j).logRows := by
    rw [edi, slice_low esi, St.pt h hst' outs_id]
  refine St.call h hst' le_pw (lo := 0) (n := 0) (by decide) (by decide) hpw hpc hpre
    (W := Z) (fun _ h ↦ h.elim) (fun _ hq ↦ ⟨changes_call hq.2.1, hq.2.2⟩)
    fun m2 hst2 hq ↦ ?_
  have hso := changes_call (m0 := m0) hq.2.1
  have hr : ewRet m2 = pwA L rows bl m0 j := by
    rw [hq.1, hpoint, edx, BitVec.toNat_ofNat, paddingWeight_mod64]
    simp only [Array.size_extract]
    omega
  exact cont m2 hst2 (call_fb h hs le_pw (by decide) (fun _ h ↦ h.elim) hso hfb')
    (call_forms h hs le_pw (by decide) hso hG') hr

end

end NativeRustcVmX64.Bus.AccumulateSide
