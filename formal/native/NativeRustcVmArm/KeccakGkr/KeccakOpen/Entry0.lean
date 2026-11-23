module

public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Ok
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Exec0

/-!
# `keccak_open`: the prologue and the plain sumcheck

`b0` saves X19 to X30 in the 2224-byte frame (`b0.take 8`), keeps the arguments in X19, X22 to
X28 and calls `sumcheck_plain(frame + 56, t, value, 3, slot, 6)` (`b0.drop 8`); after it the
state is `Sc` at `b1` (`sc_run`). The blocks reading the frame with the stack arguments above it
run from `argS` (`argS_match`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (DecArea tstateBytes TStateAt)

@[expose] public section

/-- The plain sumcheck's run. -/
def scRun (s : TState) (m0 : MachineData) : Option ((Array EW × EW) × TState) :=
  (sumcheckPlain (openValue m0) 3 qkeccakSlotBits).run s

/-- **After the plain sumcheck**, at `b1`: the body, the arguments kept, the sumcheck's output
at the frame's `56` and the slot point. -/
structure Sc [Labels] (a : DecArea) (s : TState) (m0 st : MachineData) : Prop where
  body : Body m0 st
  x19 : st.regs.X19 = m0.regs.X0
  x22 : st.regs.X22 = m0.regs.X7
  x23 : st.regs.X23 = m0.regs.X6
  x24 : st.regs.X24 = m0.regs.X5
  x25 : st.regs.X25 = m0.regs.X4
  x26 : st.regs.X26 = m0.regs.X3
  x27 : st.regs.X27 = m0.regs.X2
  x28 : st.regs.X28.toBitVec = slA m0
  out : SumcheckOut st.dmem (tA m0) a (fbA m0 + BitVec.ofNat 64 56) (slA m0) (scRun s m0)

end

public section

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- The blocks reading the stack arguments: the frame and the 32 bytes above it. -/
theorem argS_match [Labels] (h : KeccakOpenPre a s c m0) {st : MachineData} (hb : Body m0 st) :
    (Env.ofMachine st [(fbA m0, 2256)]).WF ∧ Match (Env.ofMachine st [(fbA m0, 2256)]) argS st :=
  ⟨wf_one (arg_ok h hb).1 (arg_ok h hb).2,
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (show 2224 ≤ keccakOpenStack by
      rw [stack_eq]; omega) rfl, trivial⟩ (by rw [hb.sp]; simp [Sym.eval]) trivial trivial
      trivial trivial⟩

/-- The plain sumcheck's stack in `keccak_open`'s. -/
theorem sc_le : sumcheckPlainStack ≤ 880 := by
  have := stack_eq
  unfold keccakOpenStack at this
  omega

variable [Host] {k : Nat}

/-- **The prologue and the plain sumcheck**: from the entry to `b1`. -/
theorem sc_run (hp : Placed code k) (h : KeccakOpenPre a s c m0)
    (hsc : ∀ a s, Spec (label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b1Offset) ∧ Sc a s m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b0Offset)⟩ := by
  have ok := ok_of h
  have hn := ok.nums
  have rc := rcN_of h
  have hS := h.1
  have hA := pre_areas h
  have hN := hn.hN
  have hlt : spN m0 < 2 ^ 64 := m0.regs.SP.toBitVec.isLt
  have hargW := hn.argW
  have h2224 : 2224 ≤ keccakOpenStack := by rw [stack_eq]; omega
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h2224
  have hws := wsOff h
  -- `b0.take 8`: the prologue's stores
  have hmA : Match (Env.ofMachine m0 [(fbA m0, 2224)]) frS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h2224 rfl, trivial⟩
      (by
        show _ = fbA m0 + BitVec.ofInt 64 2224
        rw [show BitVec.ofInt 64 2224 = BitVec.ofNat 64 2224 from rfl, BitVec.sub_add_cancel])
      trivial trivial trivial trivial
  have hwfA := wf_one hmap hnw
  have i0 := b0_in_code.trans hp.1 (by simp [b0])
  refine exec_then (List.IsInfixAt.trans (⟨b0.drop 8, by
    rw [List.drop_zero, List.take_append_drop]⟩ : (b0.take 8).IsInfixAt b0 0) i0 (by simp [b0]))
    run_b0a hwfA hmA
    fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show (b0.take 8).length = 8 from rfl] at hpc1
  have hb1 : Body m0 s1.data :=
    Frame.of_entry hS h2224 hm1 rfl (by decide +kernel)
      (fun r hr hr' ↦ absurd (all_slots r (by
        simp only [calleeRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with e | e | e | e | e | e | e | e | e | e | e <;> subst e <;> rfl) hr')
        (by simp))
      (by decide +kernel)
  have ts1 : TStateAt s1.data.dmem (tA m0) a s :=
    ts_keep (st := m0) hn h.2.2.1 (hm1.kept hwfA) (hm1.sameOutside hwfA) fun q hq ↦
      free_frame hn (Sumcheck.Written.inRange (r := 0) rfl hnw (by decide +kernel) hq)
  -- `b0.drop 8`: the arguments, the call
  obtain ⟨hwfB, hmB⟩ := argS_match h hb1
  refine exec_at (List.IsInfixAt.trans (⟨[], List.append_nil _⟩ : (b0.drop 8).IsInfixAt b0 8)
    i0 (by simp [b0])) run_b0b hwfB hpc1 hmB fun s2 hm2 hpc2 ↦ ?_
  have hb2 : Body m0 s2.data := hb1.of_block hmB hm2 hwfB rfl all_slots (by decide)
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwfB rfl
  have w0 : NativeRustcVm.WordAt s1.data.dmem (fbA m0 + BitVec.ofNat 64 2224)
      (openValue m0).c0 := by
    have := arg_word h hb1 (o := 0) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    exact this
  have w1 : NativeRustcVm.WordAt s1.data.dmem (fbA m0 + BitVec.ofNat 64 2232)
      (openValue m0).c1 := arg_word h hb1 (o := 8) (by decide)
  have w2 : NativeRustcVm.WordAt s1.data.dmem (fbA m0 + BitVec.ofNat 64 2240)
      (UInt64.ofBitVec (slA m0)) := arg_word h hb1 (o := 16) (by decide)
  have y0 : s2.data.regs.X0.toBitVec = fbA m0 + BitVec.ofNat 64 56 :=
    (hm2.regs .X0 _ rfl).trans (by show fbA m0 + BitVec.ofInt 64 56 = _; rfl)
  have y1 : s2.data.regs.X1.toBitVec = tA m0 := by
    show (s2.data.regs.getXReg .X1).toBitVec = _
    rw [regEq (r' := .X1) hm2 rfl, regEq (r' := .X1) hm1 rfl]
    rfl
  have y2 : s2.data.regs.X2 = (openValue m0).c0 :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X2 _ rfl).trans (Sumcheck.load_word w0))
  have y3 : s2.data.regs.X3 = (openValue m0).c1 :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X3 _ rfl).trans (Sumcheck.load_word w1))
  have y4 : s2.data.regs.X4.toNat = 3 := by
    show (s2.data.regs.getXReg .X4).toBitVec.toNat = 3
    rw [hm2.regs .X4 _ rfl]; rfl
  have y5 : s2.data.regs.X5.toBitVec = slA m0 :=
    (hm2.regs .X5 _ rfl).trans (Sumcheck.load_word w2)
  have y6 : s2.data.regs.X6.toNat = 6 := by
    show (s2.data.regs.getXReg .X6).toBitVec.toNat = 6
    rw [hm2.regs .X6 _ rfl]; rfl
  -- `sumcheck_plain`
  have hsN := sc_le
  have hks := stack_eq
  have hcs := callee_toNat ok hb2 hsN
  have hfb56 := fb_add (m0 := m0) (by omega) (o := 56) (by decide)
  have := hn.tW; have := hn.tS; have := hn.wW; have := hn.wS; have := hn.sW; have := hn.sS
  have := hn.t_s; have := hn.s_w; have := rc.st; have := rc.t; have := rc.s; have := rc.w
  have et : tstateBytes = 760 := rfl
  refine call_then hpc2 (hsc a s) ⟨hb2.stackOk hS (by decide) (by omega), ⟨?_, rc.w, ?_⟩, ?_,
    ⟨?_, ?_, ?_⟩, by rw [y4]; decide, by rw [y4]; decide, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ fun s3 hpc3 hpost3 ↦ ?_
  · have h0 := h.2.1.1
    rw [← NativeRustcVm.addr_add_zero rcAddr] at h0
    have hw := hb2.bytesAt hA hS (mem_rc (a := a) (c := c)) (o := 0)
      (by show 0 + _ ≤ 192; decide +kernel) h0
    rw [NativeRustcVm.addr_add_zero] at hw
    exact hw
  · unfold Apart; rw [hcs]; omega
  · rw [y1, hd2]; exact ts1
  · rw [y1]; unfold Apart; rw [hcs, et]; omega
  · unfold Apart; rw [hcs]; omega
  · rw [y1]; exact Areas.apart_rs hA mem_ts (mem_rc (a := a) (c := c))
  · rw [y0]; exact Mapped.kept' (NativeRustcVm.Mapped.sub hmap (o := 56) (m := 24) (by decide))
      hb2.kept
  · rw [y0]; show (fbA m0 + BitVec.ofNat 64 56).toNat + 24 ≤ 2 ^ 64; omega
  · rw [y0, y1]; unfold Apart; rw [hfb56, et]; omega
  · rw [y0]; unfold Apart; rw [hfb56]; omega
  · rw [y0]; unfold Apart; rw [hfb56, hcs]; omega
  · rw [y0]; unfold Apart; rw [hfb56]; omega
  · rw [y5, y6]; exact Mapped.kept' ok.slotM hb2.kept
  · rw [y5, y6]; show (slA m0).toNat + 16 * 6 ≤ 2 ^ 64; omega
  · rw [y5, y6, y1]; unfold Apart; rw [et]; omega
  · rw [y5, y6]; unfold Apart; omega
  · rw [y5, y6]; unfold Apart; rw [hcs]; omega
  · rw [y5, y6]; unfold Apart; omega
  · rw [y0, y5, y6]; unfold Apart; rw [hfb56]; omega
  obtain ⟨hout, hsame, hsv⟩ := hpost3
  have hR : (sumcheckPlain ⟨s2.data.regs.X2, s2.data.regs.X3⟩ s2.data.regs.X4.toNat
      s2.data.regs.X6.toNat).run s = scRun s m0 := by
    rw [y2, y3, y4, y6]
    rfl
  rw [hR, y0, y1, y5] at hout
  have hb3 : Body m0 s3.data :=
    hb2.call_local (n := sumcheckPlainStack) (lo := 2128) hS (by omega) slots_le (by decide)
      hws hsame (fun p hp ↦ by
        rcases hp with hp | hp | hp | hp
        · rw [y0, inRange_nat (x := fbA m0 + BitVec.ofNat 64 56) (n := 24) (by omega),
            hfb56] at hp
          refine .inr (.inr ((inRange_nat (show (fbA m0).toNat + 2128 ≤ 2 ^ 64 by
            rw [fb_toNat (by omega)]; omega)).mpr ?_))
          rw [fb_toNat (by omega)]
          omega
        · rw [y5, y6] at hp; exact .inr (.inl ⟨_, mem_slot, hp⟩)
        · rw [y1] at hp; exact .inr (.inl ⟨_, mem_ts, hp⟩)
        · exact .inl hp) hsv
  refine .done _ ⟨hpc3.trans (by rw [show (b0.drop 8).length = 16 from rfl, ← b0_next]; simp only [b0_length, b0Length, Nat.add_assoc]), hb3, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, hout⟩
  · exact (hsv.1 .X19 rfl).trans ((regEq (r' := .X0) hm2 rfl).trans (regEq (r' := .X0) hm1 rfl))
  · exact (hsv.1 .X22 rfl).trans ((regEq (r' := .X7) hm2 rfl).trans (regEq (r' := .X7) hm1 rfl))
  · exact (hsv.1 .X23 rfl).trans ((regEq (r' := .X6) hm2 rfl).trans (regEq (r' := .X6) hm1 rfl))
  · exact (hsv.1 .X24 rfl).trans ((regEq (r' := .X5) hm2 rfl).trans (regEq (r' := .X5) hm1 rfl))
  · exact (hsv.1 .X25 rfl).trans ((regEq (r' := .X4) hm2 rfl).trans (regEq (r' := .X4) hm1 rfl))
  · exact (hsv.1 .X26 rfl).trans ((regEq (r' := .X3) hm2 rfl).trans (regEq (r' := .X3) hm1 rfl))
  · exact (hsv.1 .X27 rfl).trans ((regEq (r' := .X2) hm2 rfl).trans (regEq (r' := .X2) hm1 rfl))
  · exact (congrArg UInt64.toBitVec (hsv.1 .X28 rfl)).trans
      ((hm2.regs .X28 _ rfl).trans (Sumcheck.load_word w2))

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
