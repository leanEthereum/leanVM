module

public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Ring.Switch.Entry

/-!
# `ring_switch`: the challenges

`stepSample` (`b2`): the buffer zeroed, `sample_challenges(t, buf, 16)`: the 16 challenges `xs`
in the frame's first 256 bytes, the `TState` the next state (`G2`).
-/

namespace NativeRustcVmArm.Ring.Switch

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.RingSwitch

@[expose] public section

/-- **After the challenges**: the frame, the `RingW` in X19, `s` in X20, the `TState` in X21
representing `s2`, the grind's `1` in X22, the challenges `xs` at the frame's base. -/
structure G2 (a : DecArea) (s2 : TState) (xs : Array EW) (m0 m : MachineData) : Prop where
  fr : SFr m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X2
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : m.regs.getXReg .X21 = m0.regs.X0
  x22 : m.regs.getXReg .X22 = 1
  ts : TStateAt m.dmem (tA m0) a s2
  ch : NativeRustcVm.EWsAt m.dmem (fb m0) xs.toList
  sz : xs.size = 16

end

public section

variable {m0 : MachineData} {a : DecArea} {s : TState}

section
variable [Labels]

/-- A range in the frame is apart from a range apart from the whole stack. -/
theorem apart_in_frame (h : RingSwitchPre a s m0) {o n : Nat} (hon : o + n ≤ 432)
    {b : BitVec 64} {k : Nat} (hb : Apart b k (stackBelow m0 ringSwitchStack) ringSwitchStack) :
    Apart (fb m0 + BitVec.ofNat 64 o) n b k := by
  have h1 := fbN h
  have h2 := hN h
  have h3 : (stackBelow m0 ringSwitchStack).toNat = m0.regs.SP.toNat - ringSwitchStack :=
    base_toNat h2
  have hSP := m0.regs.SP.toNat_lt
  have he := stack_eq
  unfold Apart at *
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- A range in the frame is apart from a callee's stack. -/
theorem apart_callee (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) {o n N' : Nat}
    (hon : o + n ≤ 432) (hle : 432 + N' ≤ ringSwitchStack) :
    Apart (fb m0 + BitVec.ofNat 64 o) n (stackBelow m N') N' := by
  have h1 := fbN h
  have h2 := hN h
  have hSP := m0.regs.SP.toNat_lt
  rw [stackBelow_eq hfr.sp (by omega)]
  have h3 := base_toNat (m0 := m0) (F := 432 + N') (by omega)
  unfold Apart
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- A frame byte is neither in a callee's stack nor an output. -/
theorem frame_safe (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) {N' : Nat}
    (hle : 432 + N' ≤ ringSwitchStack) {o n : Nat} (hon : o + n ≤ 432) {j : Nat} (hj : j < n) :
    ¬(InRange (stackBelow m N') N' (fb m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∨
      outs m0 (fb m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 j)) := by
  have hw : NoWrap (fb m0 + BitVec.ofNat 64 o) n := by
    have := fbw h
    unfold NoWrap at *
    rw [NativeRustcVm.toNat_add_ofNat (by omega)]
    omega
  rintro (hq | hq)
  · have := apart_callee h hfr hon hle
    have hsw : NoWrap (stackBelow m N') N' := by
      have := hN h
      have hSP := m0.regs.SP.toNat_lt
      rw [stackBelow_eq hfr.sp (by omega)]
      unfold NoWrap; rw [base_toNat (by omega)]; omega
    exact NativeRustcVm.Apart.not_inRange_add this hw hsw hj hq
  · rw [NativeRustcVm.addr_add_add] at hq
    exact outs_frame h _ hq (NativeRustcVm.inRange_add (by omega) (by have := fbw h; unfold NoWrap at this; omega))

/-- Bytes in the frame are kept by a call changing its stack and the outputs. -/
theorem frame_bytes_keep (h : RingSwitchPre a s m0) {m m' : MachineData} (hfr : SFr m0 m)
    {N' : Nat} (hle : 432 + N' ≤ ringSwitchStack)
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m N') N' q ∨ outs m0 q)
    {o : Nat} {bs : List UInt8} (hon : o + bs.length ≤ 432)
    (hb : NativeRustcVm.BytesAt m.dmem (fb m0 + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m'.dmem (fb m0 + BitVec.ofNat 64 o) bs :=
  NativeRustcVm.BytesAt.of_sameOutside hb hs fun _ hj ↦ frame_safe h hfr hle hon hj

/-- A callee's stack is in the whole stack. -/
theorem stack_within (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) {N' : Nat}
    (hle : 432 + N' ≤ ringSwitchStack) {q : BitVec 64} (hq : InRange (stackBelow m N') N' q) :
    Within m0 q := by
  have h2 := hN h
  have hSP := m0.regs.SP.toNat_lt
  rw [stackBelow_eq hfr.sp (by omega)] at hq
  have hnw : NoWrap (base m0 (432 + N')) N' := by
    unfold NoWrap; rw [base_toNat (by omega)]; omega
  rw [Sym.inRange_iff hnw, base_toNat (by omega)] at hq
  left
  rw [Sym.inRange_iff (nw_stack h), base_toNat h2]
  omega

end

variable [Host] {k : Nat}

/-- **The challenges** (`b2`). -/
theorem stepSample (hp : Placed code k) (h : RingSwitchPre a s m0)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s)) {s1 : TState} {m : MachineData} (hG : G1 a s1 m0 m)
    (hx0 : m.regs.X0 = okWord true) {R : MachineState → Prop}
    (cont : ∀ m' xs s2, (sampleChallenges 16).run s1 = some (xs, s2) → G2 a s2 xs m0 m' →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b3Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b2Offset)⟩ := by
  have hwf := envM_wf h hG.fr
  refine exec_then (hb b2_in_code (by simp [b2]) hp) run_b2 hwf (matchM h hG.fr)
    fun st hm1 hpc ↦ ?_
  have hfr1 : SFr m0 st.data :=
    hG.fr.ofBlockW (matchM h hG.fr) hm1 hwf rfl rfl (keep_ok (by decide) (by decide)) rfl
      (by decide) (hN h) slots_le (writeOk_low (by decide))
  have hts : TStateAt st.data.dmem (tA m0) a s1 :=
    ts_keep h hG.ts (hm1.kept hwf) (hm1.sameOutside hwf) fun q hq ↦
      frame_within h (written_frame hq rfl (by decide))
  have e0 : st.data.regs.X0 = m0.regs.X0 :=
    reg_of hm1 (r := .X0) (v := .reg .X21) rfl (by simp [Sym.eval, hG.x21])
  have e1 : st.data.regs.X1.toBitVec = fb m0 := by
    rw [show st.data.regs.X1 = st.data.regs.getXReg .X1 from rfl, hm1.regs .X1 (.ptr 0 0) rfl]
    simp [Sym.eval]
  have e2 : st.data.regs.X2 = 16 := reg_of hm1 (r := .X2) (v := .lit 16) rfl rfl
  have e22 : st.data.regs.getXReg .X22 = 1 := reg_of hm1 (v := .un .trunc .W32 (.reg .X0)) rfl (by
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [show m.regs.getXReg .X0 = m.regs.X0 from rfl, hx0]
    rfl)
  have hfw := fbw h
  have hfN := fbN h
  have hN' := hN h
  rw [stack_eq] at hN'
  have hSP := m0.regs.SP.toNat_lt
  have hout : OutOk st.data (tA m0) a (fb m0) 256 sampleChallengesStack := by
    have hf0 : fb m0 + BitVec.ofNat 64 0 = fb m0 := NativeRustcVm.addr_add_zero _
    refine ⟨fun j hj ↦ hfr1.kept _ (frame_mapped h.1 (by decide) j (by omega)),
      by unfold NoWrap at *; omega, ?_, ?_, ?_, ?_⟩
    · have := t_frame h; unfold Apart at *; omega
    · have := w_frame h; unfold Apart at *; omega
    · rw [← hf0]; exact apart_callee h hfr1 (by omega) (by decide)
    · rw [← hf0]; exact apart_in_frame h (by omega) h.2.1.2.2
  refine Fr.leafIn hfr1 (hN h) (N' := sampleChallengesStack) (lo := 0) (n := 256) (by decide)
    (by decide) keep_cs (by decide) (outs_frame h) (hsc a s1) hpc
    ⟨hfr1.stackOk h.1 (by decide) (by decide), rc_of h hfr1 (by decide),
      by show TStateAt _ st.data.regs.X0.toBitVec a s1; rw [e0]; exact hts,
      by show TStateOk _ st.data.regs.X0.toBitVec a _; rw [e0]; exact tok_of h hfr1 (by decide),
      by
        show OutOk _ st.data.regs.X0.toBitVec a st.data.regs.X1.toBitVec (16 * st.data.regs.X2.toNat) _
        rw [e0, e1, e2]; exact hout⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ by
      rw [e1, e2, NativeRustcVm.addr_add_zero] at *
      rcases hq with hq | hq | hq
      · exact .inr (.inl hq)
      · rw [e0] at hq; exact .inr (.inr (.inr hq))
      · exact .inl hq, hq.2.2⟩)
    fun m2 hfr2 hq hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingSwitch.b2Offset + b2.length = k + NativeRustcVmArm.Vm.RingSwitch.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingSwitch.b2_next]]
  obtain ⟨⟨xs, s2, hrun, hch, hts2⟩, -, -⟩ := hq
  rw [e1] at hch
  rw [e2] at hrun
  rw [e0] at hts2
  refine cont m2 xs s2 hrun {
    fr := hfr2
    x19 := by rw [hcs .X19 rfl]; exact (Match.reg_eq (matchM h hG.fr) hm1 rfl rfl).trans hG.x19
    x20 := by rw [hcs .X20 rfl]; exact (Match.reg_eq (matchM h hG.fr) hm1 rfl rfl).trans hG.x20
    x21 := by rw [hcs .X21 rfl]; exact (Match.reg_eq (matchM h hG.fr) hm1 rfl rfl).trans hG.x21
    x22 := by rw [hcs .X22 rfl]; exact e22
    ts := hts2
    ch := hch
    sz := Bus.Gkr.sampleChallenges_size hrun }

end

end NativeRustcVmArm.Ring.Switch
