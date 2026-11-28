module

public import NativeRustcVmX64.Sumcheck.RoundPoly.Frame
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# `sumcheck_round_poly` in equality mode, after `read_scalars` (x86-64)

From `b2` (`some_tail`): a rejection, or the tail's sum (`sum_e`, `b3`), the grind's bits
(`bit_length`, `b4`), the grind (`b5`), its test (`b6`), the product of the equality factor and the
sum (`EW::mul`, `b7`), the derived coefficient into the message (`b8`), the exit.
-/

namespace NativeRustcVmX64.Sumcheck.RoundPoly

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateSumcheckRoundPoly
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The equality mode's registers and frame words after `read_scalars`. -/
structure SomeAt [Labels] (m0 : MachineData) (ev : EW) (d : MachineData) : Prop where
  rf : RF m0 8 d
  r12 : reg d .r12 = tAt m0
  r13 : (reg d .r13).toNat = cnt m0 - 1
  r14 : reg d .r14 = off (msgAt m0) 16
  r15 : reg d .r15 = ev.c1.toBitVec
  w8 : NativeRustcVm.WordAt d.dmem (off (fa m0) 8) (claimOf m0).c0
  w16 : NativeRustcVm.WordAt d.dmem (off (fa m0) 16) (claimOf m0).c1
  w32 : NativeRustcVm.WordAt d.dmem (off (fa m0) 32) ev.c0

/-- After `sum_e`: the sum in RAX, RDX, RBP zero, the tail and the `TState` `s1`. -/
structure SumAt [Labels] (m0 : MachineData) (a : DecArea) (ev : EW) (tail : Array EW)
    (s1 : TState) (d : MachineData) : Prop where
  rf : RF m0 8 d
  r12 : reg d .r12 = tAt m0
  r13 : (reg d .r13).toNat = cnt m0 - 1
  r15 : reg d .r15 = ev.c1.toBitVec
  rbp : reg d .rbp = 0
  rax : reg d .rax = (sumE tail).c0.toBitVec
  rdx : reg d .rdx = (sumE tail).c1.toBitVec
  w8 : NativeRustcVm.WordAt d.dmem (off (fa m0) 8) (claimOf m0).c0
  w16 : NativeRustcVm.WordAt d.dmem (off (fa m0) 16) (claimOf m0).c1
  w32 : NativeRustcVm.WordAt d.dmem (off (fa m0) 32) ev.c0
  ts : TStateAt d.dmem (tAt m0) a s1
  tail : NativeRustcVm.EWsAt d.dmem (off (msgAt m0) 16) tail.toList

end

public section

theorem eval_cAl [Labels] (env : Env) :
    cAl.eval env = decide ((env.regs .rax).toNat % 256 = 0) :=
  testAl_eq _

theorem bitLength_le4 {n : Nat} (h : n ≤ 4) : LeanVM.Protocol.Verifier.bitLength n ≤ 64 := by
  unfold LeanVM.Protocol.Verifier.bitLength
  split
  · omega
  · have := Nat.log2_le_self n
    omega

theorem okWord_toNat (b : Bool) : (okWord b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

section
variable [Labels] {a : DecArea} {s : TState} {e : Option EW} {ev : EW} {m0 : MachineData}

/-- A body block writing only below the frame's offset `8`: the frame, its words, the `TState`
and the message's tail kept. -/
theorem RF.block0 (h : RoundPolyPre a s e m0) {d d' : MachineData} {ret : BitVec 64} {S : SState}
    (hf : RF m0 8 d) (hm : Match (envB m0 d ret) S d') {o : Nat}
    (hmid : MidOk 112 o slots S = true) (hrbx : S.reg .rbx = some (.ptr 1 0))
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 8) :
    RF m0 o d' ∧ NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) 112) := by
  have c := ctx_of h
  have hwf := wf_envB h hf.frame.kept ret
  exact ⟨(RF.block h hf hm hmid hrbx).1,
    sameOutside_low hwf hm (r := 0) rfl (hi := 112) (by omega) fun w hw' ↦
      ⟨(hw w hw').1, by have := (hw w hw').2; omega⟩⟩

end

variable [Host] {a : DecArea} {s : TState} {ev : EW} {m0 : MachineData} {k : Nat}

/-- **After the tail's sum**, at `b4`: the grind's bits, the grind, the product, the result. -/
theorem some_b4 (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (h : RoundPolyPre a s (some ev) m0) {tail : Array EW} {s1 : TState}
    (hr1 : (readScalars (cnt m0 - 1)).run s = some (tail, s1)) {d : MachineData}
    (hS : SumAt m0 a ev tail s1 d) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        RoundPolyPost a s (some ev) m0 st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b4Offset)⟩ := by
  have c := ctx_of h
  have hc2 : 2 ≤ cnt m0 := h.2.2.2.2.1
  have hc5 : cnt m0 ≤ 5 := h.2.2.2.2.2.1
  have htl : tail.size = cnt m0 - 1 := readScalars_size hr1
  have htl' : 16 + 16 * tail.toList.length ≤ 80 := by simp; omega
  have hl9 : Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9 = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b19Offset) :=
    hp.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9_at
  -- `b4`: `bit_length(count - 1)`.
  have hwf4 := wf_envB h hS.rf.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b4Offset + b4.length)).toBitVec
  refine exec_then (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf4 (fun _ _ ↦ rfl)
    (match_bodyS hS.rf _) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hw5, hW24, hrdi5, hr14_5, hk5⟩ := ok_b4
  have hf5 : RF m0 0 st5.data := (RF.block h hS.rf hm5 hmid5 (KeepsR.rbx hk5)).1
  have hs5 : NativeRustcVm.SameOutside d.dmem st5.data.dmem (NativeRustcVm.InRange (fa m0) 112) :=
    sameOutside_low hwf4 hm5 (r := 0) rfl (hi := 112) (by omega) fun w hw ↦
      ⟨(hw5 w hw).1, by rcases (hw5 w hw).2 with h' | h' <;> omega⟩
  have hin5 := writesIn_of_mid hmid5
  have hmiss5 : ∀ o, 8 ≤ o → o + 8 ≤ 24 ∨ 32 ≤ o → ∀ w ∈ (after b4 bodyS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o h1 h2 w hw _ ↦ by
    rcases (hw5 w hw).2 with h' | h' <;> omega
  have w8_5 := keepW hwf4 hm5 hin5 (by omega) (hmiss5 8 le_rfl (by omega)) hS.w8
  have w16_5 := keepW hwf4 hm5 hin5 (by omega) (hmiss5 16 (by omega) (by omega)) hS.w16
  have w32_5 := keepW hwf4 hm5 hin5 (by omega) (hmiss5 32 (by omega) (by omega)) hS.w32
  have w24_5 : NativeRustcVm.WordAt st5.data.dmem (off (fa m0) 24) (sumE tail).c1 :=
    wordAt_written hm5 (r := 0) rfl (by omega) hW24 hS.rdx
  obtain ⟨ts5, tl5⟩ := keep_ts_tail h hs5 (hm5.kept hwf4) (o0 := 16)
    (fun q hq ↦ Or.inr (frame_in h hq)) htl' (by omega) hS.ts hS.tail
  have hat5 := hf5.at h
  have r12_5 : reg st5.data .r12 = tAt m0 :=
    (hm5.regs .r12 _ (KeepsR.reg hk5 (by simp))).trans hS.r12
  have r15_5 : reg st5.data .r15 = ev.c1.toBitVec :=
    (hm5.regs .r15 _ (KeepsR.reg hk5 (by simp))).trans hS.r15
  have rbp5 : reg st5.data .rbp = 0 := (hm5.regs .rbp _ (KeepsR.reg hk5 (by simp))).trans hS.rbp
  have r14_5 : reg st5.data .r14 = (sumE tail).c0.toBitVec := (hm5.regs .r14 _ hr14_5).trans hS.rax
  have rdi5 : (reg st5.data .rdi).toNat = cnt m0 - 1 := by
    rw [show reg st5.data .rdi = _ from hm5.regs .rdi _ hrdi5]; exact hS.r13
  refine call_then hpc5 hbl (c.stackOk hat5 (by decide)) fun st6 hpc6 hrsp6 ⟨hbits, hs6, hsv6⟩ ↦ ?_
  rw [rdi5] at hbits
  have hs6' : NativeRustcVm.SameOutside st5.data.dmem st6.data.dmem (fun q ↦ False ∨
      NativeRustcVm.InRange (stackBelow st5.data bitLengthStack) bitLengthStack q) :=
    SameOutside.mono hs6 fun _ hq ↦ Or.inr hq
  have hf6 : RF m0 8 st6.data :=
    hf5.call h (Nc := bitLengthStack) (by decide) hsv6 hrsp6 (fun _ hq ↦ hq.elim) hs6'
  have kc6 := fun {o : Nat} {w : UInt64} (ho : 8 ≤ o) (hon : o + 8 ≤ 112) ↦
    keepW_call (w := w) h hat5 (Nc := bitLengthStack) (by decide) (R := fun _ ↦ False)
      (fun _ hq ↦ hq.elim) hs6' ho hon
  obtain ⟨ts6, tl6⟩ := keep_ts_tail h hs6' hsv6.2 (o0 := 16)
    (fun q hq ↦ Or.inr (hq.elim False.elim fun hq ↦ callee_in h hat5 (by decide) hq)) htl'
    (by omega) ts5 tl5
  -- `b5`: `grind(bits)`.
  have hwf6 := wf_envB h hf6.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b5Offset + b5.length)).toBitVec
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf6 (fun _ _ ↦ rfl)
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b4_next)) (match_bodyS hf6 _) fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hw7, hrdi7, hrsi7, hk7⟩ := ok_b5
  obtain ⟨hf7, hs7⟩ := RF.block0 h hf6 hm7 hmid7 (KeepsR.rbx hk7) hw7
  have hin7 := writesIn_of_mid hmid7
  have hmiss7 : ∀ o, 8 ≤ o → ∀ w ∈ (after b5 bodyS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o h1 w hw _ ↦ Or.inl (by have := (hw7 w hw).2; omega)
  obtain ⟨ts7, tl7⟩ := keep_ts_tail h hs7 (hm7.kept hwf6) (o0 := 16)
    (fun q hq ↦ Or.inr (frame_in h hq)) htl' (by omega) ts6 tl6
  have hat7 := hf7.at h
  have hb64 : LeanVM.Protocol.Verifier.bitLength (cnt m0 - 1) ≤ 64 := bitLength_le4 (by omega)
  have hrbp6 : reg st6.data .rbp = 0 := (hsv6.1 .rbp rfl).trans rbp5
  have hbits7 : grindBits st7.data = grindingBits (cnt m0 - 1 + 1) := by
    unfold grindBits
    rw [show reg st7.data .rsi = _ from hm7.regs .rsi _ hrsi7,
      eval_bitsS _ hbits hb64 hrbp6, grindingBits_succ]
    rfl
  have hrdi7' : reg st7.data .rdi = tAt m0 :=
    (hm7.regs .rdi _ hrdi7).trans ((hsv6.1 .r12 rfl).trans r12_5)
  refine call_then hpc7 (hgr a s1) ?pre fun st8 hpc8 hrsp8 hpost8 ↦ ?_
  case pre =>
    unfold GrindPre
    rw [hrdi7', hbits7, grindingBits_succ,
      show bitLenNat (cnt m0 - 1) = LeanVM.Protocol.Verifier.bitLength (cnt m0 - 1) from rfl]
    refine ⟨c.stackOk hat7 (by decide), c.rcAt hat7 (by decide), ts7,
      c.tstateOk hat7 (by decide), by omega, ?_⟩
    apply hf7.gotAt h (by decide)
    intro l hl x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact got_area h hl (by simp)
  simp only [GrindPost, hrdi7', hbits7] at hpost8
  obtain ⟨hok8, hnext8, hs8, hsv8⟩ := hpost8
  have hRt : ∀ q, NativeRustcVm.InRange (tAt m0) tstateBytes q → Chg m0 q ∧ NotHigh m0 q :=
    fun q hq ↦ ⟨Or.inr (Or.inl hq), notHigh_of_not_frame h (not_frame_t h hq)⟩
  have hf8 : RF m0 8 st8.data :=
    hf7.call h (Nc := grindStack) (by decide) hsv8 hrsp8 hRt hs8
  have kc8 := fun {o : Nat} {w : UInt64} (ho : 8 ≤ o) (hon : o + 8 ≤ 112) ↦
    keepW_call (w := w) h hat7 (Nc := grindStack) (by decide) (R := InRange (tAt m0) tstateBytes)
      (fun q hq ↦ not_frame_t h hq) hs8 ho hon
  have hrbp8 : reg st8.data .rbp = 0 :=
    (hsv8.1 .rbp rfl).trans ((hm7.regs .rbp _ (KeepsR.reg hk7 (by simp))).trans hrbp6)
  -- `b6`: the grind's test.
  have hwf8 := wf_envB h hf8.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b7Offset + b7.length)).toBitVec
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf8 nofun
    (hpc8.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b5_next)) (match_bodyS hf8 _) fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hmid9, hmem9, hk9⟩ := ok_b6
  have hf9 : RF m0 8 st9.data := (RF.block h hf8 hm9 hmid9 (KeepsR.rbx hk9)).1
  have hd9 : st9.data.dmem = st8.data.dmem := hm9.dmem_eq hwf8 hmem9
  simp only [PcOk, eval_cAl] at hpc9
  cases hr2 : (grind (grindingBits (cnt m0 - 1 + 1))).run s1 with
  | none =>
    rw [hr2] at hok8
    have hal8 : (reg st8.data .rax).toNat % 256 = 0 := hok8
    have hpc : st9.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b19Offset) := by
      rw [hpc9, show (envB m0 st8.data _).regs .rax = reg st8.data .rax from rfl, hal8]
      simp [hl9]
    obtain ⟨d9, pc9⟩ := st9
    simp only at hpc
    subst hpc
    refine Eventually.mono (exit_spec hp h hf9) fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_⟩
    refine post_none ?_ ?_ (by rw [h4]; exact hf9.same) h5
    · simp [runR, roundPoly_some_run, hr1, hr2]
    · rw [h3, show reg d9 .rbp = reg st8.data .rbp from
        hm9.regs .rbp _ (KeepsR.reg hk9 (by simp)), hrbp8]
      rfl
  | some q =>
    obtain ⟨⟨⟩, s2⟩ := q
    rw [hr2] at hok8
    have hal8 : (reg st8.data .rax).toNat % 256 = 1 := hok8
    have ts8 : TStateAt st8.data.dmem (tAt m0) a s2 := hnext8 () s2 hr2
    have tl8 : NativeRustcVm.EWsAt st8.data.dmem (off (msgAt m0) 16) tail.toList :=
      msg_keep h hs8 (by omega) (fun q hq hin ↦ hq.elim
        (fun hq ↦ (c.out_not_t (msgOk h) (msg_part h (by omega) (by omega) hin)).1 hq)
        (fun hq ↦ c.out_not_stack (msgOk h) (msg_part h (by omega) (by omega) hin)
          (callee_in h hat7 (by decide) hq))) tl7
    have hpc : st9.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b7Offset) := by
      rw [hpc9, show (envB m0 st8.data _).regs .rax = reg st8.data .rax from rfl, hal8]
      rfl
    -- `b7`: `EW::mul(eq, sum)`.
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf8 (fun _ _ ↦ rfl) hpc hm9
      fun st10 hm10 hpc10 ↦ ?_
    obtain ⟨hmid10, hw10, hrdi10, hrsi10, hrdx10, hrcx10, hk10⟩ := ok_b7
    obtain ⟨hf10, hs10⟩ := RF.block0 h hf8 hm10 hmid10 (KeepsR.rbx hk10) hw10
    have hin10 := writesIn_of_mid hmid10
    have hmiss10 : ∀ o, 8 ≤ o → ∀ w ∈ (after b7 (after b6 bodyS)).mem, w.r = 0 →
        w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o h1 w hw _ ↦
      Or.inl (by have := (hw10 w hw).2; omega)
    have w32_8 := kc8 (by omega) (by omega)
      (keepW hwf6 hm7 hin7 (by omega) (hmiss7 32 (by omega)) (kc6 (by omega) (by omega) w32_5))
    have w24_8 := kc8 (by omega) (by omega)
      (keepW hwf6 hm7 hin7 (by omega) (hmiss7 24 (by omega)) (kc6 (by omega) (by omega) w24_5))
    have w8_8 := kc8 (by omega) (by omega)
      (keepW hwf6 hm7 hin7 (by omega) (hmiss7 8 le_rfl) (kc6 (by omega) (by omega) w8_5))
    have w16_8 := kc8 (by omega) (by omega)
      (keepW hwf6 hm7 hin7 (by omega) (hmiss7 16 (by omega)) (kc6 (by omega) (by omega) w16_5))
    have hrdi : reg st10.data .rdi = ev.c0.toBitVec :=
      (hm10.regs .rdi _ hrdi10).trans (load_ofMachine (o := 32) rfl w32_8)
    have hrcx : reg st10.data .rcx = (sumE tail).c1.toBitVec :=
      (hm10.regs .rcx _ hrcx10).trans (load_ofMachine (o := 24) rfl w24_8)
    have hrsi : reg st10.data .rsi = ev.c1.toBitVec :=
      (hm10.regs .rsi _ hrsi10).trans ((hsv8.1 .r15 rfl).trans
        ((hm7.regs .r15 _ (KeepsR.reg hk7 (by simp))).trans ((hsv6.1 .r15 rfl).trans r15_5)))
    have hrdx : reg st10.data .rdx = (sumE tail).c0.toBitVec :=
      (hm10.regs .rdx _ hrdx10).trans ((hsv8.1 .r14 rfl).trans
        ((hm7.regs .r14 _ (KeepsR.reg hk7 (by simp))).trans ((hsv6.1 .r14 rfl).trans r14_5)))
    have hat10 := hf10.at h
    refine call_then hpc10 hmul (c.stackOk hat10 (by decide))
      fun st11 hpc11 hrsp11 ⟨hm0', hm1', hs11, hsv11⟩ ↦ ?_
    rw [hrdi, hrsi, hrdx, hrcx] at hm0' hm1'
    have hs11' : NativeRustcVm.SameOutside st10.data.dmem st11.data.dmem (fun q ↦ False ∨
        NativeRustcVm.InRange (stackBelow st10.data ewMulStack) ewMulStack q) :=
      SameOutside.mono hs11 fun _ hq ↦ Or.inr hq
    have hf11 : RF m0 8 st11.data :=
      hf10.call h (Nc := ewMulStack) (by decide) hsv11 hrsp11 (fun _ hq ↦ hq.elim) hs11'
    have kc11 := fun {o : Nat} {w : UInt64} (ho : 8 ≤ o) (hon : o + 8 ≤ 112) ↦
      keepW_call (w := w) h hat10 (Nc := ewMulStack) (by decide) (R := fun _ ↦ False)
        (fun _ hq ↦ hq.elim) hs11' ho hon
    have w8_11 := kc11 (by omega) (by omega)
      (keepW hwf8 hm10 hin10 (by omega) (hmiss10 8 le_rfl) w8_8)
    have w16_11 := kc11 (by omega) (by omega)
      (keepW hwf8 hm10 hin10 (by omega) (hmiss10 16 (by omega)) w16_8)
    obtain ⟨ts10, tl10⟩ := keep_ts_tail h hs10 (hm10.kept hwf8) (o0 := 16)
      (fun q hq ↦ Or.inr (frame_in h hq)) htl' (by omega) ts8 tl8
    obtain ⟨ts11, tl11⟩ := keep_ts_tail h hs11' hsv11.2 (o0 := 16)
      (fun q hq ↦ Or.inr (hq.elim False.elim fun hq ↦ callee_in h hat10 (by decide) hq)) htl'
      (by omega) ts10 tl10
    -- `b8`: the derived coefficient into `msg[0]`, `Some`.
    have hwf11 := wf_envB h hf11.frame.kept 0
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf11 nofun
      (hpc11.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b7_next)) (match_bodyS hf11 _) fun st12 hm12 hpc12 ↦ ?_
    obtain ⟨hmid12, hw12, hW0, hW8, hrbp12, hrbx12⟩ := ok_b8
    have hf12 : RF m0 8 st12.data := (RF.block h hf11 hm12 hmid12 hrbx12).1
    have hs12 : NativeRustcVm.SameOutside st11.data.dmem st12.data.dmem
        (NativeRustcVm.InRange (msgAt m0) 16) :=
      sameOutside_low hwf11 hm12 (r := 1) rfl (hi := 16) (by omega) hw12
    obtain ⟨ts12, tl12⟩ := keep_ts_tail h hs12 (hm12.kept hwf11) (o0 := 16)
      (fun q hq ↦ Or.inl hq) htl' (by omega) ts11 tl11
    have hhead : NativeRustcVm.EWAt st12.data.dmem (msgAt m0) (claimOf m0 + ev * sumE tail) := by
      rw [ewAt_iff]
      have e0 := wordAt_written hm12 (r := 1) (o := 0) rfl (by omega) hW0
        (w := (claimOf m0 + ev * sumE tail).c0) (by
          simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
          rw [load_ofMachine (o := 8) rfl w8_11, show st11.data.regs.get64 .rax = _ from hm0']
          show _ = (UInt64.ofBitVec (reg m0 .rdx) ^^^ (ev * sumE tail).c0).toBitVec
          rw [UInt64.toBitVec_xor, BitVec.xor_comm]
          rfl)
      have e1 := wordAt_written hm12 (r := 1) (o := 8) rfl (by omega) hW8
        (w := (claimOf m0 + ev * sumE tail).c1) (by
          simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
          rw [load_ofMachine (o := 16) rfl w16_11, show st11.data.regs.get64 .rdx = _ from hm1']
          show _ = (UInt64.ofBitVec (reg m0 .rcx) ^^^ (ev * sumE tail).c1).toBitVec
          rw [UInt64.toBitVec_xor, BitVec.xor_comm]
          rfl)
      rw [off_zero] at e0
      exact ⟨e0, e1⟩
    simp only [PcOk] at hpc12
    rw [hl9] at hpc12
    obtain ⟨d12, pc12⟩ := st12
    simp only at hpc12
    subst hpc12
    refine Eventually.mono (exit_spec hp h hf12) fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_⟩
    refine post_some (msg := #[claimOf m0 + ev * sumE tail] ++ tail) (s' := s2) ?_ ?_ ?_
      (by rw [h4]; exact ts12) (by rw [h4]; exact hf12.same) h5
    · simp [runR, roundPoly_some_run, hr1, hr2]
    · rw [h3, show reg d12 .rbp = _ from hm12.regs .rbp _ hrbp12]
      exact merge_one _
    · rw [h4, Array.toList_append]
      exact ewsAt_cons.mpr ⟨hhead, by simpa using tl12⟩

/-- **After `read_scalars`**, at `b2`: the tail's sum, or a rejection. -/
theorem some_tail (hp : Placed code k)
    (hsum : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (h : RoundPolyPre a s (some ev) m0) {d : MachineData} (hS : SomeAt m0 ev d)
    (hal : (reg d .rax).toNat % 256 =
      (okWord ((readScalars (cnt m0 - 1)).run s).isSome).toNat)
    (htail : ∀ tail s1, (readScalars (cnt m0 - 1)).run s = some (tail, s1) →
      NativeRustcVm.EWsAt d.dmem (off (msgAt m0) 16) tail.toList ∧
        TStateAt d.dmem (tAt m0) a s1) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        RoundPolyPost a s (some ev) m0 st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b2Offset)⟩ := by
  have c := ctx_of h
  have hc2 : 2 ≤ cnt m0 := h.2.2.2.2.1
  have hc5 : cnt m0 ≤ 5 := h.2.2.2.2.2.1
  have hl9 : Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9 = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b19Offset) :=
    hp.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9_at
  -- `b2`: `read_scalars`' test.
  have hwf1 := wf_envB h hS.rf.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b3Offset + b3.length)).toBitVec
  refine exec_then (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf1 nofun
    (match_bodyS hS.rf _) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hmem2, hrbp2, hk2⟩ := ok_b2
  simp only [PcOk, eval_cAl] at hpc2
  cases hr1 : (readScalars (cnt m0 - 1)).run s with
  | none =>
    rw [hr1] at hal
    have hpc : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b19Offset) := by
      rw [hpc2, show (envB m0 d _).regs .rax = reg d .rax from rfl, hal]
      exact (ite_eq_left_iff.mpr (fun h ↦ absurd (by decide) h)).trans hl9
    have hf2 : RF m0 8 st2.data := (RF.block h hS.rf hm2 hmid2 (KeepsR.rbx hk2)).1
    have hd2 : st2.data.dmem = d.dmem := hm2.dmem_eq hwf1 hmem2
    obtain ⟨d2, pc2⟩ := st2
    simp only at hpc
    subst hpc
    refine Eventually.mono (exit_spec hp h hf2) fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_⟩
    refine post_none ?_ ?_ (by rw [h4]; exact hf2.same) h5
    · simp [runR, roundPoly_some_run, hr1]
    · rw [h3, show reg d2 .rbp = _ from hm2.regs .rbp _ hrbp2]
      rfl
  | some p =>
    obtain ⟨tail, s1⟩ := p
    rw [hr1] at hal
    obtain ⟨htl, hts⟩ := htail tail s1 hr1
    have hsz : tail.size = cnt m0 - 1 := readScalars_size hr1
    have htl' : 16 + 16 * tail.toList.length ≤ 80 := by simp; omega
    have hpc : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b3Offset) := by
      rw [hpc2, show (envB m0 d _).regs .rax = reg d .rax from rfl, hal]
      rfl
    -- `b3`: `sum_e(tail)`.
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf1 (fun _ _ ↦ rfl) hpc hm2
      fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hmid3, hw3, hrbp3, hrdi3, hrsi3, hk3⟩ := ok_b3
    obtain ⟨hf3, hs3⟩ := RF.block0 h hS.rf hm3 hmid3 (KeepsR.rbx hk3) hw3
    have hin3 := writesIn_of_mid hmid3
    have hmiss3 : ∀ o, 8 ≤ o → ∀ w ∈ (after b3 (after b2 bodyS)).mem, w.r = 0 →
        w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o h1 w hw _ ↦
      Or.inl (by have := (hw3 w hw).2; omega)
    obtain ⟨ts3, tl3⟩ := keep_ts_tail h hs3 (hm3.kept hwf1) (o0 := 16)
      (fun q hq ↦ Or.inr (frame_in h hq)) htl' (by omega) hts htl
    have hat3 := hf3.at h
    have hrdi : reg st3.data .rdi = off (msgAt m0) 16 := (hm3.regs .rdi _ hrdi3).trans hS.r14
    have hrsi : (reg st3.data .rsi).toNat = cnt m0 - 1 := by
      rw [show reg st3.data .rsi = _ from hm3.regs .rsi _ hrsi3]; exact hS.r13
    have ho := msgOut h hat3 (Nc := sumEStack) (by decide) (o := 16) (n := 16 * (cnt m0 - 1))
      (by omega) (by omega)
    refine call_then hpc3 hsum ?pre fun st4 hpc4 hrsp4 ⟨hsumv, hs4, hsv4⟩ ↦ ?_
    case pre =>
      unfold SumEPre
      rw [hrdi, hrsi]
      exact ⟨c.stackOk hat3 (by decide), by omega, ho.1, ho.2.1⟩
    have hsl : slice st3.data (reg st3.data .rdi) (reg st3.data .rsi) = tail := by
      unfold slice
      rw [hrsi, hrdi, show cnt m0 - 1 = tail.toList.length by simp [hsz],
        NativeRustcVm.ewsOf_of_ewsAt tl3]
    rw [hsl] at hsumv
    have hs4' : NativeRustcVm.SameOutside st3.data.dmem st4.data.dmem (fun q ↦
        NativeRustcVm.InRange 0 0 q ∨
          NativeRustcVm.InRange (stackBelow st3.data sumEStack) sumEStack q) := hs4
    have hR0 : ∀ q, NativeRustcVm.InRange 0 0 q → False := fun q hq ↦ by
      unfold NativeRustcVm.InRange at hq; omega
    have hf4 : RF m0 8 st4.data :=
      hf3.call h (Nc := sumEStack) (by decide) hsv4 hrsp4 (fun q hq ↦ (hR0 q hq).elim) hs4'
    have kc4 := fun {o : Nat} {w : UInt64} (ho : 8 ≤ o) (hon : o + 8 ≤ 112) ↦
      keepW_call (w := w) h hat3 (Nc := sumEStack) (by decide) (R := NativeRustcVm.InRange 0 0)
        (fun q hq ↦ (hR0 q hq).elim) hs4' ho hon
    obtain ⟨ts4, tl4⟩ := keep_ts_tail h hs4' hsv4.2 (o0 := 16)
      (fun q hq ↦ hq.elim (fun hq ↦ (hR0 q hq).elim)
        fun hq ↦ Or.inr (callee_in h hat3 (by decide) hq)) htl' (by omega) ts3 tl3
    have hkeep : ∀ r, r ∈ [Reg64.r12, .r13, .r14, .r15] → reg st4.data r = reg d r :=
      fun r hr ↦ (hsv4.1 r (by revert hr; decide +revert)).trans
        (hm3.regs r _ (KeepsR.reg hk3 hr))
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc4
    subst hpc4
    rw [NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b3_length]
    exact some_b4 hp hbl hgr hmul h hr1 ⟨hf4, (hkeep .r12 (by simp)).trans hS.r12,
      by rw [hkeep .r13 (by simp)]; exact hS.r13, (hkeep .r15 (by simp)).trans hS.r15,
      (hsv4.1 .rbp rfl).trans (hm3.regs .rbp _ hrbp3),
      by rw [← hsumv]; rfl, by rw [← hsumv]; rfl,
      kc4 (by omega) (by omega) (keepW hwf1 hm3 hin3 (by omega) (hmiss3 8 le_rfl) hS.w8),
      kc4 (by omega) (by omega) (keepW hwf1 hm3 hin3 (by omega) (hmiss3 16 (by omega)) hS.w16),
      kc4 (by omega) (by omega) (keepW hwf1 hm3 hin3 (by omega) (hmiss3 32 (by omega)) hS.w32),
      ts4, tl4⟩

end

end NativeRustcVmX64.Sumcheck.RoundPoly
