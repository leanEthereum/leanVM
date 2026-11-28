module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Entry0
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.SlotPre
public import NativeRustcVm.Top.Phases
public import NativeRustcVmX64.Code.Vm.SlotWeights.Names

/-! # `keccak_open`: successful sumcheck and slot weights -/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr DecArea tstateBytes TStateAt Touch)

@[expose] public section

abbrev swOf (c : KeccakClaimW) (m0 : MachineData) : Array (Array EW) :=
  keccakSlotWeights (reg m0 .rdx).toNat c (openFirst m0).toNat (openCount m0).toNat

structure Sw [Labels] (a : DecArea) (c : KeccakClaimW) (m0 : MachineData) (s1 : TState)
    (sl : Array EW) (v : EW) (d : MachineData) : Prop where
  body : Body m0 8 d
  bx : reg d .rbx = oA m0
  r15 : reg d .r15 = rwA m0
  v0 : NativeRustcVm.WordAt d.dmem (off (fbA m0) 80) v.c0
  v1 : NativeRustcVm.WordAt d.dmem (off (fbA m0) 72) v.c1
  sl_size : sl.size = 6
  slot : NativeRustcVm.EWsAt d.dmem (slA m0) sl.toList
  ts : TStateAt d.dmem (tA m0) a s1
  rows : NativeRustcVm.EWsAt d.dmem (rwA m0) (NativeRustcVm.KeccakGkr.rowsFlat (swOf c m0))

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem sw_run (hp : Placed code k) (h : PreOk a s c m0)
    (hsw : ∀ c, Spec (Labels.label NativeRustcVmX64.Vm.SlotWeights.entryLabel) (SlotWeightsPre c) (SlotWeightsPost c))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b1Offset)) (hsc : Sc a s m0 st.data)
    {s1 : TState} {sl : Array EW} {v : EW} (hrun : scRun s m0 = some ((sl, v), s1)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b4Offset) ∧ Sw a c m0 s1 sl v st'.data) st := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.s; have := hn.t; have := hn.w; have := hn.a
  have := hn.ss; have := hn.st; have := hn.sw; have := hn.sa; have := hn.sw'; have := hn.tw
  have := hn.wa
  have hfb := fbA_toNat h
  have hout := hsc.out.1
  rw [hrun] at hout
  obtain ⟨htag, hval⟩ := hout
  have hval' := NativeRustcVm.ewAt_iff.mp hval
  rw [off_off, off_add] at hval'
  have hsl := hsc.out.2.1 sl v s1 hrun
  have hts := hsc.out.2.2 _ s1 hrun
  have hsz : sl.size = 6 := by
    have hh := (NativeRustcVm.Top.sumcheck_size (openValue m0) 3
      (Array.replicate LeanVM.Protocol.Verifier.qkeccakSlotBits none)).gives s _ s1 hrun
    simpa [NativeVm.Math.Keccak.qkeccakSlotBits_eq] using hh
  have hwf := wf_fold h hsc.body.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) x1 hwf nofun hpc
    (body_match h hsc.body) fun st1 hm1 hpc1 ↦ ?_
  have hl : (E m0 st.data (fun _ ↦ 0) 0).load 0 88 4 = 1#64 := load4_of_tag (.inr rfl) htag
  have ht : (SBool.not (.cmp .eq .W32 (.load 0 88 4) (.lit 1))).eval
      (E m0 st.data (fun _ ↦ 0) 0) = false := by
    simp only [SBool.eval, Sym.eval, hl]; decide +kernel
  have hp1 : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b2Offset) := by
    simp only [PcOk, ht, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b1_next)
  have hd1 := hm1.dmem_eq hwf f1.2.2.1
  have hb1 := body_unchanged h hsc.body hm1 f1.2.1 f1.2.2.1
  have regs1 : ∀ r ∈ [.rbx, .rbp, .r12, .r13, .r14], reg st1.data r = reg st.data r := by
    intro r hr
    exact hm1.regs r _ (by
      have hh := List.all_eq_true.mp f1.2.2.2 r hr
      simpa only [beq_iff_eq] using hh)
  have hwf1 := wf_fold h hb1.fr.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b2Offset + b2.length)).toBitVec)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) x2 hwf1 (fun _ _ ↦ rfl) hp1
    (body_match h hb1) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨_, hmid2, hwrites, hw8, hw72, hw80, hdi, hsi, hdx, hcx, h8, h9, h15, hkeep⟩ := f2
  have hb2 := body_block h hb1 hm2 hmid2 (fun w hw ↦ by
    have := hwrites w hw; exact ⟨this.1, by omega⟩)
  have hs2 := sameOutside_touch hwf1 hm2 (r := 0) (b := fbA m0) (N := 2216)
    (lo := 0) (hi := 88) rfl (by decide) (fun w hw ↦ by
      have := hwrites w hw; exact ⟨this.1, by omega⟩)
  have hv0 : NativeRustcVm.WordAt st2.data.dmem (off (fbA m0) 80) v.c0 := by
    have hh := wordAt_write hm2 (r := 0) (o := 80) (v := .load 0 96 8) rfl (by decide) hw80
    change NativeRustcVm.WordAt _ _ (UInt64.ofBitVec ((E m0 st1.data (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b2Offset + b2.length)).toBitVec).load 0 96 8)) at hh
    rw [load_of_wordAt (w := v.c0) (by
      change NativeRustcVm.WordAt st1.data.dmem (off (fbA m0) 96) v.c0
      rw [hd1]; exact hval'.1), UInt64.ofBitVec_toBitVec] at hh
    exact hh
  have hv1 : NativeRustcVm.WordAt st2.data.dmem (off (fbA m0) 72) v.c1 := by
    have hh := wordAt_write hm2 (r := 0) (o := 72) (v := .load 0 104 8) rfl (by decide) hw72
    change NativeRustcVm.WordAt _ _ (UInt64.ofBitVec ((E m0 st1.data (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b2Offset + b2.length)).toBitVec).load 0 104 8)) at hh
    rw [load_of_wordAt (w := v.c1) (by
      change NativeRustcVm.WordAt st1.data.dmem (off (fbA m0) 104) v.c1
      rw [hd1]; exact hval'.2), UInt64.ofBitVec_toBitVec] at hh
    exact hh
  have ydi : reg st2.data .rdi = reg m0 .rdx :=
    (hm2.regs .rdi _ hdi).trans ((regs1 .rbp (by simp)).trans hsc.bp)
  have ysi : reg st2.data .rsi = reg m0 .rcx :=
    (hm2.regs .rsi _ hsi).trans ((regs1 .r13 (by simp)).trans hsc.r13)
  have ydx : reg st2.data .rdx = reg m0 .r8 :=
    (hm2.regs .rdx _ hdx).trans ((regs1 .r12 (by simp)).trans hsc.r12)
  have ycx : reg st2.data .rcx = reg m0 .r9 :=
    (hm2.regs .rcx _ hcx).trans ((regs1 .r14 (by simp)).trans hsc.r14)
  have y8 : reg st2.data .r8 = openFirst m0 :=
    (hm2.regs .r8 _ h8).trans (load_arg h hb1.same (i := 0) (by decide))
  have y9 : reg st2.data .r9 = openCount m0 :=
    (hm2.regs .r9 _ h9).trans (load_arg h hb1.same (i := 1) (by decide))
  have y15 : reg st2.data .r15 = rwA m0 :=
    (hm2.regs .r15 _ h15).trans (load_arg h hb1.same (i := 5) (by decide))
  have ybx : reg st2.data .rbx = oA m0 :=
    (hm2.regs .rbx (.reg .rbx) (by
      have hh := List.all_eq_true.mp hkeep .rbx (by simp)
      simpa only [beq_iff_eq] using hh)).trans ((regs1 .rbx (by simp)).trans hsc.bx)
  have yw : NativeRustcVm.WordAt st2.data.dmem (off (fbA m0) 8) (UInt64.ofBitVec (rwA m0)) := by
    have hh := wordAt_write hm2 (r := 0) (o := 8) (v := .load 3 40 8) rfl (by decide) hw8
    change NativeRustcVm.WordAt _ _ (UInt64.ofBitVec ((E m0 st1.data (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b2Offset + b2.length)).toBitVec).load 3 40 8)) at hh
    rw [load_arg h hb1.same (i := 5) (by decide)] at hh
    exact hh
  have hat := hb2.at h
  have ya : stackArg st2.data 0 = rwA m0 := by
    unfold stackArg
    rw [hat.sp, show stackBelow m0 2208 + BitVec.ofNat 64 (8 + 8 * 0) = off (fbA m0) 8 from rfl,
      NativeRustcVm.wordOf_of_wordAt yw, UInt64.toBitVec_ofBitVec]
  refine call_then hpc2 (hsw c) (slot_pre h hb2 ydi ysi ydx ycx y8 y9 ya)
    fun st3 hpc3 hrsp3 hpost ↦ ?_
  obtain ⟨hal, hrows, hsame, hsv⟩ := hpost
  change NativeRustcVm.EWsAt st3.data.dmem (stackArg st2.data 0) _ at hrows
  rw [ya, ydi, y8, y9] at hrows
  change NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
    (fun q ↦ ∃ r : NativeRustcVm.Region, r ∈ [⟨stackBelow st2.data slotWeightsStack, slotWeightsStack⟩,
      ⟨stackArg st2.data 0, 65536⟩] ∧ r.Holds q) at hsame
  have hso3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem (fun q ↦
      NativeRustcVm.InRange (stackBelow st2.data slotWeightsStack) slotWeightsStack q ∨
      NativeRustcVm.InRange (rwA m0) 65536 q) := by
    intro q hq
    apply hsame q
    rintro ⟨r, hr, hqr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hq (.inl hqr)
    · rw [ya] at hqr; exact hq (.inr hqr)
  have hle : 2208 + slotWeightsStack ≤ keccakOpenStack := by decide
  have hsafe3 : ∀ q, (NativeRustcVm.InRange (stackBelow st2.data slotWeightsStack) slotWeightsStack q ∨
      NativeRustcVm.InRange (rwA m0) 65536 q) → Safe m0 q := by
    intro q hq
    rcases hq with hq | hq
    · have hs := ((context h).inRange_callee hat hle hq).1
      have htop := (context h).fr
      rw [stack_eq, inRange_iff' (by
        have := stack_noWrap h.st; rwa [stack_eq] at this),
        stackBelow_toNat (by omega)] at hs
      have hbelow : q.toNat < (fbA m0).toNat := by
        have hc : (stackBelow st2.data slotWeightsStack).toNat =
            (rspOf m0).toNat - (2208 + slotWeightsStack) := by
          have hbound : 2208 + slotWeightsStack ≤ (rspOf m0).toNat := by
            have hstack : slotWeightsStack ≤ 992 := by decide
            omega
          rw [stackBelow_callee hat.sp hbound, stackBelow_toNat hbound]
        rw [inRange_iff' (by
          have hh := stack_noWrap ((context h).stackOk hat hle); exact hh), hc] at hq
        have : slotWeightsStack ≤ 992 := by decide
        omega
      exact .inl ⟨hs.1, by omega⟩
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq
      exact .inr (.inr hq)
  have hf3 := hb2.fr.call hsv hrsp3 hso3 (fun q hq hfr ↦ by
    have hh := hsafe3 q hq
    rw [inRange_iff' (by have := (context h).noWrap_frame; exact this), hfb] at hfr
    rcases hq with hq | hq
    · exact ((context h).inRange_callee hat hle hq).2 (by
        rw [inRange_iff' (context h).noWrap_frame, hfb]; exact hfr)
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq
      omega) (context h).noWrap_frame slots_le'
  have hb3 : Body m0 8 st3.data := ⟨hf3, fun q hq ↦
    (hso3 q fun ht ↦ hq (safe_out h (hsafe3 q ht))).trans (hb2.same q hq)⟩
  have vkeep : ∀ {o : Nat} {w : UInt64}, 64 ≤ o → o + 8 ≤ 112 →
      NativeRustcVm.WordAt st2.data.dmem (off (fbA m0) o) w →
      NativeRustcVm.WordAt st3.data.dmem (off (fbA m0) o) w := by
    intro o w ho hon hw
    refine bytes_keep hso3 hsafe3 (by rw [NativeRustcVm.length_wordBytes, fb_off h (by omega)]; omega)
      (fun y h1 h2 hy ↦ ?_) hw
    rw [NativeRustcVm.length_wordBytes, fb_off h (by omega)] at h2
    rw [fb_off h (by omega)] at h1
    unfold SafeN at hy
    omega
  have hsl2 : NativeRustcVm.EWsAt st2.data.dmem (slA m0) sl.toList := by
    refine bytesAt_congr (show NativeRustcVm.EWsAt st1.data.dmem (slA m0) sl.toList from
      by rw [hd1]; exact hsl) fun i hi ↦ hs2 _ fun ⟨j, hj, hlow, he⟩ ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz] at hi
    have he' := congrArg BitVec.toNat he
    rw [fb_off h (by omega), show slA m0 + BitVec.ofNat 64 i = off (slA m0) i from rfl,
      toNat_off (by omega)] at he'
    omega
  have hts2 : TStateAt st2.data.dmem (tA m0) a s1 := by
    refine (show TStateAt st1.data.dmem (tA m0) a s1 by rw [hd1]; exact hts).frame
      (hm2.kept hwf1) (fun q hq ↦ (context h).stack_not_t ?_) hs2
    obtain ⟨j, hj, hlow, rfl⟩ := hq
    exact (context h).inRange_frame (NativeRustcVm.Transcript.inRange_off_self (by omega)
      (by have := (context h).noWrap_frame; unfold NativeRustcVm.NoWrap at this; omega))
  have hsl3 : NativeRustcVm.EWsAt st3.data.dmem (slA m0) sl.toList := by
    refine bytes_keep hso3 hsafe3 (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz]; omega)
      (fun y h1 h2 hy ↦ ?_) hsl2
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz] at h2
    unfold SafeN at hy
    omega
  have hts3 : TStateAt st3.data.dmem (tA m0) a s1 := by
    refine hts2.frame hsv.2 (fun q hq ↦ ?_) hso3
    have hh := hsafe3 q hq
    unfold Safe SafeN at hh
    constructor
    · rw [show tstateBytes = 760 from rfl, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
      omega
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
      omega
  have hwf3 := wf_fold h hb3.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  have hp3 : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b3Offset) := hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b2_next)
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) x3 hwf3 nofun hp3
    (body_match h hb3) fun st4 hm4 hpc4 ↦ ?_
  have ht3 : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (E m0 st3.data (fun _ ↦ 0) 0) = false := by
    have hh : low .W8 (reg st3.data .rax) = 1#8 := by
      apply BitVec.eq_of_toNat_eq
      change (reg st3.data .rax).toNat % 256 = 1
      exact hal
    simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply]
    change (low .W8 (ext .W8 (low .W8 (reg st3.data .rax) &&& low .W8 (reg st3.data .rax))) ==
      low .W8 0#64) = false
    rw [hh]
    decide +kernel
  have hd4 := hm4.dmem_eq hwf3 f3.2.2.1
  have hb4 := body_unchanged h hb3 hm4 f3.2.1 f3.2.2.1
  have hp4 : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b4Offset) := by
    simp only [PcOk, ht3, Bool.false_eq_true, ↓reduceIte] at hpc4
    exact hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b3_next)
  refine .done _ ⟨hp4, hb4, ?_, ?_, ?_, ?_, hsz, ?_, ?_, ?_⟩
  · exact (hm4.regs .rbx (.reg .rbx) (by rw [after_eq e3]; rfl)).trans ((hsv.1 .rbx rfl).trans ybx)
  · exact (hm4.regs .r15 (.reg .r15) (by rw [after_eq e3]; rfl)).trans ((hsv.1 .r15 rfl).trans y15)
  · rw [hd4]; exact vkeep (by decide) (by decide) hv0
  · rw [hd4]; exact vkeep (by decide) (by decide) hv1
  · rw [hd4]; exact hsl3
  · rw [hd4]; exact hts3
  · rw [hd4]; exact hrows

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
