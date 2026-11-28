module

public import NativeRustcVmX64.Bus.AccumulateSide.TurnF
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names

/-! # `accumulate_side`: advancing the table loop (x86-64) -/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

 theorem low_b27 : lowW' (after b27 aS) := by
  rw [after_eq run_b27]; decide +kernel

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

 theorem turnG (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (outs m0) (VT L rows bl Fm SL m0 j) D26c 8 m)
    (hG : FormsAt m.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 (j + 1)).1)
    (hret : ewRet m = tsel SL (ptA m0) j * pwA L rows bl m0 j * (evA L rows bl m0 j + 1)) :
    Eventually (step1 Host.exe) (fun st ↦ TH L rows bl Fm SL m0 (j + 1) st.data ∧
      ((st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b17Offset) ∧ j + 1 < bl.length) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b28Offset) ∧ j + 1 = bl.length)))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b27Offset)⟩ := by
  let V := VT L rows bl Fm SL m0 j
  let V' := VT L rows bl Fm SL m0 (j + 1)
  let env := frameEnv m0 m F [(rspOf m0 + 8#64, 88)] (fun _ ↦ 0) 0
  have hwf : env.WF := wf1 h hst.fr.kept h.argsIn
  obtain ⟨hmid, hw, htr, hsi, hdx, h12⟩ := ok_b27
  refine St.run h (rest := [(rspOf m0 + 8#64, 88)]) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b27_in_code (by simp [b27]) hp) exit_b27 nofun hst.fr hst.same
    (((hst.hd.reg0 (rs' := [(fb m0, F + 8), (rspOf m0 + 8#64, 88)]) (by decide) rfl).append
      (St.holdsDA h hst outs_id)).append
      holdsDl) (by decide) hwf
    (St.mt hst ⟨rfl, rfl, trivial⟩ trivial trivial argAliases_ok) hmid hw (by decide) htr
    fun st hm hpc hst' _ ↦ ?_
  have hk := run_keep hwf hm low_b27 (writesIn_of_mid hmid)
  have g120 : env.load 0 120 8 = BitVec.ofNat 64 (16 * j) :=
    hst.hd.load (r := 0) (o := 120) (i := 32) (by decide)
  have g40 : env.load 0 40 8 = BitVec.ofNat 64 (16 * bl.length) := by
    change (Env.ofMachine m [(fb m0, F + 8)]).load 0 40 8 = _
    rw [hst.hd.load (r := 0) (o := 40) (i := 25) (by decide)]
    change BitVec.ofNat 64 (16 * (reg m0 .r8).toNat) = _
    rw [h.r8]
  have e12 : st.data.regs.get64 .r12 = (V' 32).toBitVec := by
    rw [hm.regs .r12 _ h12]
    change BinOp.apply .add .W64 (BitVec.ofNat 64 16) (env.load 0 120 8) = _
    rw [add64, g120, ← BitVec.ofNat_add]
    change BitVec.ofNat 64 (16 + 16 * j) = BitVec.ofNat 64 (16 * (j + 1))
    congr 1; omega
  have esi : st.data.regs.get64 .rsi = (V' 33).toBitVec := by
    rw [hm.regs .rsi _ hsi]
    change BinOp.apply .xor .W64 ((Env.ofMachine m [(fb m0, F + 8)]).load 0 56 8) (m.regs.get64 .rax) = _
    rw [xor64, hst.hd.load (r := 0) (o := 56) (i := 33) (by decide), ewRet_c0 hret]
    change (stA L rows bl Fm SL m0 j).2.c0.toBitVec ^^^ _ = (stA L rows bl Fm SL m0 (j + 1)).2.c0.toBitVec
    rw [stA_succ_snd, add_c0, UInt64.toBitVec_xor]
  have edx : st.data.regs.get64 .rdx = (V' 34).toBitVec := by
    rw [hm.regs .rdx _ hdx]
    change BinOp.apply .xor .W64 ((Env.ofMachine m [(fb m0, F + 8)]).load 0 128 8) (m.regs.get64 .rdx) = _
    rw [xor64, hst.hd.load (r := 0) (o := 128) (i := 34) (by decide), ewRet_c1 hret]
    change (stA L rows bl Fm SL m0 j).2.c1.toBitVec ^^^ _ = (stA L rows bl Fm SL m0 (j + 1)).2.c1.toBitVec
    rw [stA_succ_snd, add_c1, UInt64.toBitVec_xor]
  have e14 : st.data.regs.get64 .r14 = (V' 35).toBitVec := hst'.hd.reg (r := .r14) (i := 45) (by decide)
  have e15 : st.data.regs.get64 .r15 = (V' 36).toBitVec := hst'.hd.reg (r := .r15) (i := 46) (by decide)
  have hfixed : St m0 (outs m0) V DTf 8 st.data := St.sub hst' (by decide)
  have hnext : St m0 (outs m0) V' DT 8 st.data := St.add hfixed
    (fun p hp ↦ Vt_lt (by revert p hp; decide))
    (holds_reg (i := 32) e12 (holds_reg (i := 33) esi (holds_reg (i := 34) edx
      (holds_reg (i := 35) e14 (holds_reg (i := 36) e15 (holds_nil _ _ _))))))
  refine .done _ ⟨⟨hnext, KeepF.forms h hk hG⟩, ?_⟩
  have hbl := h.bl51
  have hc : c27.eval env = decide (j + 1 ≠ bl.length) := by
    change (!(CmpOp.apply .eq .W64 (env.load 0 40 8)
      (BinOp.apply .add .W64 (BitVec.ofNat 64 16) (env.load 0 120 8)))) = _
    rw [eq64, add64, g40, g120, ← BitVec.ofNat_add]
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_iff]
    constructor
    · intro hne heq; exact hne (by rw [← heq]; congr 1; omega)
    · intro hne heq
      have hx := congrArg BitVec.toNat heq
      rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at hx
      exact hne (by omega)
  change st.pc = (if c27.eval env = true then Labels.label NativeRustcVmX64.Vm.AccumulateSide.label_15 else Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b28Offset)) at hpc
  rw [hc] at hpc
  by_cases he : j + 1 = bl.length
  · right; exact ⟨by simpa [he] using hpc, he⟩
  · left
    have hl : Labels.label NativeRustcVmX64.Vm.AccumulateSide.label_15 = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b17Offset) :=
      hp.label NativeRustcVmX64.Vm.AccumulateSide.label_15_at
    exact ⟨by simpa [he, hl] using hpc, by omega⟩

end

end NativeRustcVmX64.Bus.AccumulateSide
