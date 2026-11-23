module

public import NativeRustcVmX64.Bus.AccumulateSide.TurnE
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Evaluate.Names

/-! # `accumulate_side`: the padding row's contribution (x86-64) -/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

 theorem mul_ret {m m' : MachineData} {a b : EW} (h : EWMulPost m m')
    (hdi : reg m .rdi = a.c0.toBitVec) (hsi : reg m .rsi = a.c1.toBitVec)
    (hdx : reg m .rdx = b.c0.toBitVec) (hcx : reg m .rcx = b.c1.toBitVec) : ewRet m' = a * b := by
  apply ew_ext
  · change UInt64.ofBitVec (reg m' .rax) = _
    rw [h.1, hdi, hsi, hdx, hcx]; rfl
  · change UInt64.ofBitVec (reg m' .rdx) = _
    rw [h.2.1, hdi, hsi, hdx, hcx]; rfl

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

 theorem turnF (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (outs m0) (VT L rows bl Fm SL m0 j) D23c 8 m)
    (hfb : FB m0 m.dmem (fmA L rows bl m0 j))
    (hG : FormsAt m.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 (j + 1)).1)
    (hret : ewRet m = pwA L rows bl m0 j)
    {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (outs m0) (VT L rows bl Fm SL m0 j) D26c 8 m2 →
      FormsAt m2.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 (j + 1)).1 →
      ewRet m2 = tsel SL (ptA m0) j * pwA L rows bl m0 j * (evA L rows bl m0 j + 1) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b27Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b24Offset)⟩ := by
  let V := VT L rows bl Fm SL m0 j
  obtain ⟨hmid1, hw1, htr1⟩ := ok_b24
  refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b24Offset + b24.length)).toBitVec)
    rfl (infix_of b24_in_code (by simp [b24]) hp) exit_b24 (fun _ _ ↦ rfl) hst.fr hst.same
    ((hst.hd.append (holds_reg (V := V) (i := 48) (ewRet_c0 hret)
      (holds_reg (i := 49) (ewRet_c1 hret) (holds_nil _ _ _)))).reg0 (by decide) rfl) (by decide)
    (wf0 h hst.fr.kept) (St.mt hst ⟨rfl, trivial⟩ trivial trivial trivial) hmid1 hw1 (by decide) htr1
    fun st1 hm1 hpc1 hst1 _ ↦ ?_
  have hk1 := run_keep (wf0 h hst.fr.kept) hm1 low_T.2.2.2.2.2.2.2.2.2.1 (writesIn_of_mid hmid1)
  have hs1 : rspOf st1.data = fb m0 := by rw [hst1.fr.sp, off_zero]
  have edi1 := hst1.hd.reg (r := .rdi) (i := 37) (by decide)
  have esi1 := hst1.hd.reg (r := .rsi) (i := 38) (by decide)
  have edx1 := hst1.hd.reg (r := .rdx) (i := 48) (by decide)
  have ecx1 := hst1.hd.reg (r := .rcx) (i := 49) (by decide)
  have hst1c : St m0 (outs m0) V D23c 0 st1.data := St.sub hst1 (by decide)
  refine St.call h hst1c le_mul (lo := 0) (n := 0) (by decide) (by decide) hmul hpc1
    (St.stackOk h hst1c le_mul) (W := Z) (fun _ h ↦ h.elim)
    (fun _ hq ↦ ⟨same_call hq.2.2.1, hq.2.2.2⟩) fun m2 hst2 hq2 ↦ ?_
  have hret2 := mul_ret hq2 edi1 esi1 edx1 ecx1
  have hso2 := same_call (m0 := m0) hq2.2.2.1
  have hfb2 := call_fb h hs1 le_mul (by decide) (fun _ h ↦ h.elim) hso2 (KeepF.fbuf hk1 hfb)
  have hG2 := call_forms h hs1 le_mul (by decide) hso2 (KeepF.forms h hk1 hG)
  show Eventually _ _ (⟨m2, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b25Offset)⟩ : MachineState)
  obtain ⟨hmid3, hw3, htr3⟩ := ok_b25
  refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b25Offset + b25.length)).toBitVec)
    rfl (infix_of b25_in_code (by simp [b25]) hp) exit_b25 (fun _ _ ↦ rfl) hst2.fr hst2.same
    ((hst2.hd.append (holds_reg (V := V) (i := 50) (ewRet_c0 hret2)
      (holds_reg (i := 51) (ewRet_c1 hret2) (holds_nil _ _ _)))).reg0 (by decide) rfl) (by decide)
    (wf0 h hst2.fr.kept) (St.mt hst2 ⟨rfl, trivial⟩ trivial trivial trivial) hmid3 hw3 (by decide) htr3
    fun st3 hm3 hpc3 hst3 _ ↦ ?_
  have hk3 := run_keep (wf0 h hst2.fr.kept) hm3 low_T.2.2.2.2.2.2.2.2.2.2.1 (writesIn_of_mid hmid3)
  have hfb3 := KeepF.fbuf hk3 hfb2
  have hG3 := KeepF.forms h hk3 hG2
  have hs3 : rspOf st3.data = fb m0 := by rw [hst3.fr.sp, off_zero]
  have edi3 : reg st3.data .rdi = off (fb m0) 6064 := hst3.hd.reg (r := .rdi) (i := 42) (by decide)
  have esi3 : reg st3.data .rsi = BitVec.ofNat 64 (fmA L rows bl m0 j).size :=
    hst3.hd.reg (r := .rsi) (i := 41) (by decide)
  have edx3 := hst3.hd.reg (r := .rdx) (i := 47) (by decide)
  have ecx3 := hst3.hd.reg (r := .rcx) (i := 44) (by decide)
  have ho : (bkA L rows bl j).owner < 6 := by
    change ((BA L rows bl).getD j default).owner < 6
    rw [BA_getD L rows bl hj]; exact (h.bown _ (List.getElem_mem hj)).1
  have hpad := padding_slice (St.rodata h hst3 outs_id le_ev) ho edx3 (congrArg BitVec.toNat ecx3)
  have hsize : (fmA L rows bl m0 j).size ≤ 148 := hfb3.len_le
  have hterms := inOk_prefix (frame_inOk h hst3.fr.kept hs3 le_ev (o := 6064) (n := 5920)
    (by decide) (by decide) (by decide)) (show termBytes * (fmA L rows bl m0 j).size ≤ 5920 by
      unfold termBytes; omega)
  have hpre : EvaluatePre (fmA L rows bl m0 j) st3.data := by
    refine ⟨St.stackOk h hst3 le_ev, ?_, ?_, ?_, ?_, hpad.1⟩
    · rw [esi3, toNat_ofNat_lt (by omega)]
    · rw [edi3, ← off_off (fb m0) 6056 8]
      exact hfb3.terms
    · rw [edi3, esi3, toNat_ofNat_lt (by omega)]; exact hterms.1
    · rw [edi3, esi3, toNat_ofNat_lt (by omega)]; exact hterms.2
  have hst3c : St m0 (outs m0) V D25c 0 st3.data := St.sub hst3 (by decide)
  refine St.call h hst3c le_ev (lo := 0) (n := 0) (by decide) (by decide) (hev _) hpc3 hpre
    (W := Z) (fun _ h ↦ h.elim) (fun _ hq ↦ ⟨changes_call hq.2.1, hq.2.2⟩)
    fun m4 hst4 hq4 ↦ ?_
  have hr4 : ewRet m4 = evA L rows bl m0 j := hq4.1.trans (congrArg _ hpad.2)
  have hG4 := call_forms h hs3 le_ev (by decide) (changes_call hq4.2.1) hG3
  show Eventually _ _ (⟨m4, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b26Offset)⟩ : MachineState)
  obtain ⟨hmid5, hw5, htr5, hdx5⟩ := ok_b26
  refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b26Offset + b26.length)).toBitVec)
    rfl (infix_of b26_in_code (by simp [b26]) hp) exit_b26 (fun _ _ ↦ rfl) hst4.fr hst4.same
    ((hst4.hd.append (holds_reg (V := V) (i := 53) (ewRet_c1 hr4) (holds_nil _ _ _))).reg0
      (by decide) rfl) (by decide) (wf0 h hst4.fr.kept)
    (St.mt hst4 ⟨rfl, trivial⟩ trivial trivial trivial) hmid5 hw5 (by decide) htr5
    fun st5 hm5 hpc5 hst5 _ ↦ ?_
  have hk5 := run_keep (wf0 h hst4.fr.kept) hm5 low_T.2.2.2.2.2.2.2.2.2.2.2 (writesIn_of_mid hmid5)
  have hs5 : rspOf st5.data = fb m0 := by rw [hst5.fr.sp, off_zero]
  have edi5 := hst5.hd.reg (r := .rdi) (i := 50) (by decide)
  have esi5 := hst5.hd.reg (r := .rsi) (i := 51) (by decide)
  have edx5 : reg st5.data .rdx = (evA L rows bl m0 j + 1).c0.toBitVec := by
    change st5.data.regs.get64 .rdx = _
    rw [hm5.regs .rdx _ hdx5]
    change BinOp.apply .xor .W64 (m4.regs.get64 .rax) (BitVec.ofNat 64 1) = _
    rw [xor64, ewRet_c0 hr4, add_c0, UInt64.toBitVec_xor]; rfl
  have ecx5 : reg st5.data .rcx = (evA L rows bl m0 j + 1).c1.toBitVec := by
    change st5.data.regs.get64 .rcx = _
    rw [hst5.hd.reg (r := .rcx) (i := 53) (by decide), add_c1, c1_one, UInt64.xor_zero]; rfl
  have hst5c : St m0 (outs m0) V D26c 0 st5.data := St.sub hst5 (by decide)
  refine St.call h hst5c le_mul (lo := 0) (n := 0) (by decide) (by decide) hmul hpc5
    (St.stackOk h hst5c le_mul) (W := Z) (fun _ h ↦ h.elim)
    (fun _ hq ↦ ⟨same_call hq.2.2.1, hq.2.2.2⟩) fun m6 hst6 hq6 ↦ ?_
  exact cont m6 hst6 (call_forms h hs5 le_mul (by decide) (same_call hq6.2.2.1)
    (KeepF.forms h hk5 hG4)) (mul_ret hq6 edi5 esi5 edx5 ecx5)

end

end NativeRustcVmX64.Bus.AccumulateSide
