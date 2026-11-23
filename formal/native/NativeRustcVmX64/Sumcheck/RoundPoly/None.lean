module

public import NativeRustcVmX64.Sumcheck.RoundPoly.Some
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# `sumcheck_round_poly` in plain mode (x86-64)

From `b10` after `read_scalar` (`none_b10`): a rejection, or the constant into `msg[0]` and
`read_scalars` of the tail (`b11`); its test (`b12`), the claim's limb `0` saved and the tail's
sum (`sum_e`, `b13`); from `b14` (`none_b14`): the grind's bits (`bit_length`), the grind
(`b15`), its test (`b16`), the derived coefficient into `msg[1]` (`b17`), the exit.
-/

namespace NativeRustcVmX64.Sumcheck.RoundPoly

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateSumcheckRoundPoly
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- After `read_scalar`. -/
structure NoneAt [Labels] (m0 : MachineData) (a : DecArea) (s : TState) (d : MachineData) :
    Prop where
  rf : RF m0 8 d
  r12 : reg d .r12 = tAt m0
  r13 : (reg d .r13).toNat = cnt m0
  r14 : reg d .r14 = reg m0 .rcx
  r15 : reg d .r15 = reg m0 .rdx
  out : OptEWAt d.dmem (off (fa m0) 40) ((readScalar.run s).map (·.1))
  next : NextAt d.dmem (tAt m0) a (readScalar.run s)

/-- After `sum_e` in plain mode: the constant `x0`, the tail, their `TState` `s1`. -/
structure NSumAt [Labels] (m0 : MachineData) (a : DecArea) (x0 : EW) (tail : Array EW)
    (s1 : TState) (d : MachineData) : Prop where
  rf : RF m0 8 d
  r12 : reg d .r12 = tAt m0
  r13 : (reg d .r13).toNat = cnt m0 - 2
  rbp : reg d .rbp = 0
  rax : reg d .rax = (sumE tail).c0.toBitVec
  rdx : reg d .rdx = (sumE tail).c1.toBitVec
  w8 : NativeRustcVm.WordAt d.dmem (off (fa m0) 8) (claimOf m0).c0
  w16 : NativeRustcVm.WordAt d.dmem (off (fa m0) 16) (claimOf m0).c1
  ts : TStateAt d.dmem (tAt m0) a s1
  head : NativeRustcVm.EWsAt d.dmem (off (msgAt m0) 0) [x0]
  tail : NativeRustcVm.EWsAt d.dmem (off (msgAt m0) 32) tail.toList

end

public section

section
variable [Labels] {a : DecArea} {s : TState} {e : Option EW} {m0 : MachineData}

/-- **The constant kept** where the memory changed only in the message from `16`, the `TState` and
the stack. -/
theorem keep_head (h : RoundPolyPre a s e m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (off (msgAt m0) 16) 64 q ∨
      NativeRustcVm.InRange (tAt m0) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q)
    {x0 : EW} (hx : NativeRustcVm.EWsAt d (off (msgAt m0) 0) [x0]) :
    NativeRustcVm.EWsAt d' (off (msgAt m0) 0) [x0] := by
  have c := ctx_of h
  refine msg_keep h hs (by simp) (fun q hq hin ↦ ?_) hx
  simp only [List.length_cons, List.length_nil] at hin
  rcases hR q hq with h1 | h1 | h1
  · exact msg_parts h (o1 := 0) (n1 := 16 * (0 + 1)) (o2 := 16) (n2 := 64) (by omega) (by omega)
      hin h1
  · exact (c.out_not_t (msgOk h) (msg_part h (by omega) (by omega) hin)).1 h1
  · exact c.out_not_stack (msgOk h) (msg_part h (by omega) (by omega) hin) h1

end

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

/-- **After the tail's sum** in plain mode, at `b14`: the grind's bits, the grind, the derived
coefficient. -/
theorem none_b14 (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (h : RoundPolyPre a s none m0) {x0 : EW} {s0 : TState}
    (hr0 : readScalar.run s = some (x0, s0)) {tail : Array EW} {s1 : TState}
    (hr1 : (readScalars (cnt m0 - 2)).run s0 = some (tail, s1)) {d : MachineData}
    (hS : NSumAt m0 a x0 tail s1 d) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        RoundPolyPost a s none m0 st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b14Offset)⟩ := by
  have c := ctx_of h
  have hc2 : 2 ≤ cnt m0 := h.2.2.2.2.1
  have hc5 : cnt m0 ≤ 5 := h.2.2.2.2.2.1
  have htl : tail.size = cnt m0 - 2 := readScalars_size hr1
  have htl' : 32 + 16 * tail.toList.length ≤ 80 := by simp; omega
  have hl9 : Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9 = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b19Offset) :=
    hp.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9_at
  -- `b14`: `bit_length(count - 2)`.
  have hwf4 := wf_envB h hS.rf.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b14Offset + b14.length)).toBitVec
  refine exec_then (infix_of b14_in_code (by simp [b14]) hp) exit_b14 hwf4 (fun _ _ ↦ rfl)
    (match_bodyS hS.rf _) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hw5, hrdi5, hr14_5, hr15_5, hk5⟩ := ok_b14
  obtain ⟨hf5, hs5⟩ := RF.block0 h hS.rf hm5 hmid5 (KeepsR.rbx hk5) hw5
  have hin5 := writesIn_of_mid hmid5
  have hmiss5 : ∀ o, 8 ≤ o → ∀ w ∈ (after b14 bodyS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o h1 w hw _ ↦ Or.inl (by have := (hw5 w hw).2; omega)
  have hRf : ∀ q, NativeRustcVm.InRange (fa m0) 112 q →
      NativeRustcVm.InRange (off (msgAt m0) 16) 64 q ∨ NativeRustcVm.InRange (tAt m0) tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q :=
    fun q hq ↦ Or.inr (Or.inr (frame_in h hq))
  obtain ⟨ts5, tl5⟩ := keep_ts_tail h hs5 (hm5.kept hwf4) (o0 := 32)
    (fun q hq ↦ Or.inr (frame_in h hq)) htl' (by omega) hS.ts hS.tail
  have hd5 := keep_head h hs5 hRf hS.head
  have hat5 := hf5.at h
  have rbp5 : reg st5.data .rbp = 0 := (hm5.regs .rbp _ (KeepsR.reg hk5 (by simp))).trans hS.rbp
  have r12_5 : reg st5.data .r12 = tAt m0 :=
    (hm5.regs .r12 _ (KeepsR.reg hk5 (by simp))).trans hS.r12
  have r14_5 : reg st5.data .r14 = (sumE tail).c1.toBitVec := (hm5.regs .r14 _ hr14_5).trans hS.rdx
  have r15_5 : reg st5.data .r15 = (sumE tail).c0.toBitVec := (hm5.regs .r15 _ hr15_5).trans hS.rax
  have rdi5 : (reg st5.data .rdi).toNat = cnt m0 - 2 := by
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
  have hR6 : ∀ q, (False ∨
      NativeRustcVm.InRange (stackBelow st5.data bitLengthStack) bitLengthStack q) →
      NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q :=
    fun q hq ↦ hq.elim False.elim fun hq ↦ callee_in h hat5 (by decide) hq
  obtain ⟨ts6, tl6⟩ := keep_ts_tail h hs6' hsv6.2 (o0 := 32) (fun q hq ↦ Or.inr (hR6 q hq)) htl'
    (by omega) ts5 tl5
  have hd6 := keep_head h hs6' (fun q hq ↦ Or.inr (Or.inr (hR6 q hq))) hd5
  -- `b15`: `grind(bits)`.
  have hwf6 := wf_envB h hf6.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b15Offset + b15.length)).toBitVec
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf6 (fun _ _ ↦ rfl)
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b14_next)) (match_bodyS hf6 _) fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hw7, hrdi7, hrsi7, hk7⟩ := ok_b15
  obtain ⟨hf7, hs7⟩ := RF.block0 h hf6 hm7 hmid7 (KeepsR.rbx hk7) hw7
  have hin7 := writesIn_of_mid hmid7
  have hmiss7 : ∀ o, 8 ≤ o → ∀ w ∈ (after b15 bodyS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o h1 w hw _ ↦ Or.inl (by have := (hw7 w hw).2; omega)
  obtain ⟨ts7, tl7⟩ := keep_ts_tail h hs7 (hm7.kept hwf6) (o0 := 32)
    (fun q hq ↦ Or.inr (frame_in h hq)) htl' (by omega) ts6 tl6
  have hd7 := keep_head h hs7 hRf hd6
  have hat7 := hf7.at h
  have hb64 : LeanVM.Protocol.Verifier.bitLength (cnt m0 - 2) ≤ 64 := bitLength_le4 (by omega)
  have hrbp6 : reg st6.data .rbp = 0 := (hsv6.1 .rbp rfl).trans rbp5
  have hbits7 : grindBits st7.data = grindingBits (cnt m0 - 1) := by
    unfold grindBits
    rw [show reg st7.data .rsi = _ from hm7.regs .rsi _ hrsi7,
      eval_bitsS _ hbits hb64 hrbp6, show cnt m0 - 1 = cnt m0 - 2 + 1 by omega, grindingBits_succ]
    rfl
  have hrdi7' : reg st7.data .rdi = tAt m0 :=
    (hm7.regs .rdi _ hrdi7).trans ((hsv6.1 .r12 rfl).trans r12_5)
  refine call_then hpc7 (hgr a s1) ?pre fun st8 hpc8 hrsp8 hpost8 ↦ ?_
  case pre =>
    unfold GrindPre
    rw [hrdi7', hbits7, show cnt m0 - 1 = cnt m0 - 2 + 1 by omega, grindingBits_succ,
      show bitLenNat (cnt m0 - 2) = LeanVM.Protocol.Verifier.bitLength (cnt m0 - 2) from rfl]
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
  have hR8 : ∀ q, (NativeRustcVm.InRange (tAt m0) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow st7.data grindStack) grindStack q) →
      NativeRustcVm.InRange (off (msgAt m0) 16) 64 q ∨ NativeRustcVm.InRange (tAt m0) tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 roundPolyStack) roundPolyStack q :=
    fun q hq ↦ hq.elim (fun hq ↦ Or.inr (Or.inl hq))
      fun hq ↦ Or.inr (Or.inr (callee_in h hat7 (by decide) hq))
  have hd8 := keep_head h hs8 hR8 hd7
  have hrbp8 : reg st8.data .rbp = 0 :=
    (hsv8.1 .rbp rfl).trans ((hm7.regs .rbp _ (KeepsR.reg hk7 (by simp))).trans hrbp6)
  have hr14_8 : reg st8.data .r14 = (sumE tail).c1.toBitVec :=
    (hsv8.1 .r14 rfl).trans ((hm7.regs .r14 _ (KeepsR.reg hk7 (by simp))).trans
      ((hsv6.1 .r14 rfl).trans r14_5))
  have hr15_8 : reg st8.data .r15 = (sumE tail).c0.toBitVec :=
    (hsv8.1 .r15 rfl).trans ((hm7.regs .r15 _ (KeepsR.reg hk7 (by simp))).trans
      ((hsv6.1 .r15 rfl).trans r15_5))
  have w8_8 := kc8 (by omega) (by omega)
    (keepW hwf6 hm7 hin7 (by omega) (hmiss7 8 le_rfl)
      (kc6 (by omega) (by omega) (keepW hwf4 hm5 hin5 (by omega) (hmiss5 8 le_rfl) hS.w8)))
  have w16_8 := kc8 (by omega) (by omega)
    (keepW hwf6 hm7 hin7 (by omega) (hmiss7 16 (by omega))
      (kc6 (by omega) (by omega) (keepW hwf4 hm5 hin5 (by omega) (hmiss5 16 (by omega)) hS.w16)))
  -- `b16`: the grind's test.
  have hwf8 := wf_envB h hf8.frame.kept 0
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) exit_b16 hwf8 nofun
    (hpc8.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b15_next)) (match_bodyS hf8 _) fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hmid9, hmem9, hk9⟩ := ok_b16
  have hf9 : RF m0 8 st9.data := (RF.block h hf8 hm9 hmid9 (KeepsR.rbx hk9)).1
  simp only [PcOk, eval_cAl] at hpc9
  cases hr2 : (grind (grindingBits (cnt m0 - 1))).run s1 with
  | none =>
    rw [hr2] at hok8
    have hal8 : (reg st8.data .rax).toNat % 256 = 0 := hok8
    have hpc : st9.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b19Offset) := by
      rw [hpc9, show (envB m0 st8.data _).regs .rax = reg st8.data .rax from rfl, hal8]
      exact (ite_eq_left_iff.mpr (fun h ↦ absurd (by decide) h)).trans hl9
    obtain ⟨d9, pc9⟩ := st9
    simp only at hpc
    subst hpc
    refine Eventually.mono (exit_spec hp h hf9) fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_⟩
    refine post_none ?_ ?_ (by rw [h4]; exact hf9.same) h5
    · simp [runR, roundPoly_none_run, hr0, hr1, hr2]
    · rw [h3, show reg d9 .rbp = reg st8.data .rbp from
        hm9.regs .rbp _ (KeepsR.reg hk9 (by simp)), hrbp8]
      rfl
  | some q =>
    obtain ⟨⟨⟩, s2⟩ := q
    rw [hr2] at hok8
    have hal8 : (reg st8.data .rax).toNat % 256 = 1 := hok8
    have ts8 : TStateAt st8.data.dmem (tAt m0) a s2 := hnext8 () s2 hr2
    have tl8 : NativeRustcVm.EWsAt st8.data.dmem (off (msgAt m0) 32) tail.toList :=
      msg_keep h hs8 (by omega) (fun q hq hin ↦ hq.elim
        (fun hq ↦ (c.out_not_t (msgOk h) (msg_part h (by omega) (by omega) hin)).1 hq)
        (fun hq ↦ c.out_not_stack (msgOk h) (msg_part h (by omega) (by omega) hin)
          (callee_in h hat7 (by decide) hq))) tl7
    have hpc : st9.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b17Offset) := by
      rw [hpc9, show (envB m0 st8.data _).regs .rax = reg st8.data .rax from rfl, hal8]
      rfl
    -- `b17`: the derived coefficient into `msg[1]`, `Some`.
    refine exec_at (infix_of b17_in_code (by simp [b17]) hp) exit_b17 hwf8 nofun hpc hm9
      fun st10 hm10 hpc10 ↦ ?_
    obtain ⟨hmid10, hw10, hW16, hW24, hrbp10, hrbx10⟩ := ok_b17
    have hf10 : RF m0 8 st10.data := (RF.block h hf8 hm10 hmid10 hrbx10).1
    have hs10 := sameOutside_touch hwf8 hm10 (r := 1) rfl (by omega) hw10
    have hR10 : ∀ q, Touch (msgAt m0) 80 (fun j ↦ 16 ≤ j ∧ j < 32) q →
        NativeRustcVm.InRange (off (msgAt m0) 16) 16 q := fun q hq ↦ touch_msg h (by omega) hq
    obtain ⟨ts10, tl10⟩ := keep_ts_tail h hs10 (hm10.kept hwf8) (o0 := 32)
      (fun q hq ↦ Or.inl (by
        have := msg_part h (o := 16) (n := 16) (by omega) (by omega) (hR10 q hq)
        have h2 := hR10 q hq
        have hnw := msg_noWrap h
        unfold NativeRustcVm.NoWrap at hnw
        rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
          toNat_off (by omega)] at h2
        rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
        omega)) htl' (by omega) ts8 tl8
    have hd10 := keep_head h hs10 (fun q hq ↦ Or.inl (by
      have h2 := hR10 q hq
      have hnw := msg_noWrap h
      unfold NativeRustcVm.NoWrap at hnw
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
        toNat_off (by omega)] at h2
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
        toNat_off (by omega)]
      omega)) hd8
    have hmid : NativeRustcVm.EWAt st10.data.dmem (off (msgAt m0) 16) (claimOf m0 + sumE tail) := by
      rw [ewAt_iff]
      have e0 := wordAt_written hm10 (r := 1) (o := 16) rfl (by omega) hW16
        (w := (claimOf m0 + sumE tail).c0) (by
          simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
          rw [load_ofMachine (o := 8) rfl w8_8, show st8.data.regs.get64 .r15 = _ from hr15_8]
          show _ = (UInt64.ofBitVec (reg m0 .rdx) ^^^ (sumE tail).c0).toBitVec
          rw [UInt64.toBitVec_xor, BitVec.xor_comm])
      have e1 := wordAt_written hm10 (r := 1) (o := 24) rfl (by omega) hW24
        (w := (claimOf m0 + sumE tail).c1) (by
          simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
          rw [load_ofMachine (o := 16) rfl w16_8, show st8.data.regs.get64 .r14 = _ from hr14_8]
          show _ = (UInt64.ofBitVec (reg m0 .rcx) ^^^ (sumE tail).c1).toBitVec
          rw [UInt64.toBitVec_xor, BitVec.xor_comm])
      exact ⟨e0, by rw [off_off]; exact e1⟩
    simp only [PcOk] at hpc10
    rw [hl9] at hpc10
    obtain ⟨d10, pc10⟩ := st10
    simp only at hpc10
    subst hpc10
    refine Eventually.mono (exit_spec hp h hf10) fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_⟩
    refine post_some (msg := #[x0, claimOf m0 + sumE tail] ++ tail) (s' := s2) ?_ ?_ ?_
      (by rw [h4]; exact ts10) (by rw [h4]; exact hf10.same) h5
    · simp [runR, roundPoly_none_run, hr0, hr1, hr2]
    · rw [h3, show reg d10 .rbp = _ from hm10.regs .rbp _ hrbp10]
      exact merge_one _
    · rw [h4, Array.toList_append]
      have hx := (ewsAt_cons.mp hd10).1
      rw [off_zero] at hx
      refine ewsAt_cons.mpr ⟨hx, ewsAt_cons.mpr ⟨hmid, ?_⟩⟩
      rw [off_off]
      simpa using tl10

end

end NativeRustcVmX64.Sumcheck.RoundPoly
