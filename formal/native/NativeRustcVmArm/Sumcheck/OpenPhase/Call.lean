module

public import NativeRustcVmArm.Sumcheck.OpenPhase.Start

/-!
# `open_phase`: what a climb's calls are given and keep

The phase's bytes from offset `c` (`ph_*`) and the frame's from offset `o` (`fr_*`): their
addresses, apart from a callee's stack, mapped, kept. A call writing 32 bytes of the frame
(below its slots) and its stack keeps the frame and the frame's other bytes (`afterCall`); a
step keeping the callee-saved registers and the frame's first 16 bytes keeps the climbs'
invariant (`CInv.keep`).
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.OpenPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol LeanVM.Protocol.Compile NativeVm

public section

variable [Labels] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 m : MachineData}

/-! ## The phase's bytes -/

theorem ph_toNat (hpre : OpenPhasePre P R Q m0) {c : Nat} (hc : c < 8 * phaseWords) :
    (phO m0 + BitVec.ofNat 64 c).toNat = (phO m0).toNat + c := by
  obtain ⟨-, -, -, -, -, -, -, hnwp, -⟩ := id hpre
  have h' : (phO m0).toNat + 8 * phaseWords ≤ 2 ^ 64 := hnwp
  exact NativeRustcVm.toNat_add_ofNat (by omega)

theorem ph_noWrap (hpre : OpenPhasePre P R Q m0) {c n : Nat} (hcn : c + n ≤ 8 * phaseWords) :
    NoWrap (phO m0 + BitVec.ofNat 64 c) n :=
  NativeRustcVm.NoWrap.sub hpre.2.2.2.2.2.2.2.1 hcn

theorem ph_apart (hpre : OpenPhasePre P R Q m0) {c n : Nat} (hc : c < 8 * phaseWords)
    (hcn : c + n ≤ 8 * phaseWords) :
    Apart (phO m0 + BitVec.ofNat 64 c) n (stackBelow m0 openPhaseStack) openPhaseStack := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, haps, -⟩ := id hpre
  have e := ph_toNat hpre hc
  have haps' : (phO m0).toNat + 8 * phaseWords ≤ (stackBelow m0 openPhaseStack).toNat ∨
      (stackBelow m0 openPhaseStack).toNat + openPhaseStack ≤ (phO m0).toNat := haps
  unfold Apart
  rw [e]
  omega

/-- The phase's bytes, apart from a callee's stack. -/
theorem ph_apart_callee (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 m) {c n N' : Nat}
    (hc : c < 8 * phaseWords) (hcn : c + n ≤ 8 * phaseWords) (hle : 176 + N' ≤ openPhaseStack) :
    Apart (phO m0 + BitVec.ofNat 64 c) n (stackBelow m N') N' :=
  hf.apart (hN hpre) (ph_apart hpre hc hcn) hle

theorem ph_mapped (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 m) {c n : Nat}
    (hcn : c + n ≤ 8 * phaseWords) : Mapped m.dmem (phO m0 + BitVec.ofNat 64 c) n := by
  obtain ⟨-, -, -, -, -, -, hmp, -⟩ := id hpre
  intro i hi
  rw [NativeRustcVm.addr_add_add]
  exact hf.kept _ (hmp _ (by omega))

/-- The phase's bytes, kept in a state of the frame. -/
theorem ph_keep (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 m) {c n : Nat}
    (hc : c < 8 * phaseWords) (hcn : c + n ≤ 8 * phaseWords) {bs : List UInt8}
    (hle : bs.length ≤ n) (h : NativeRustcVm.BytesAt m0.dmem (phO m0 + BitVec.ofNat 64 c) bs) :
    NativeRustcVm.BytesAt m.dmem (phO m0 + BitVec.ofNat 64 c) bs :=
  keep hpre hf (ph_noWrap hpre hcn) (ph_apart hpre hc hcn) hle h

/-! ## The frame's bytes -/

theorem fr_toNat (hpre : OpenPhasePre P R Q m0) {o : Nat} (ho : o ≤ 176) :
    (base m0 176 + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - 176 + o := by
  have h1 := hN hpre
  rw [openPhaseStack_eq] at h1
  have hl := m0.regs.SP.toNat_lt
  rw [NativeRustcVm.toNat_add_ofNat (by rw [base_toNat (m0 := m0) (F := 176) (by omega)]; omega),
    base_toNat (m0 := m0) (F := 176) (by omega)]

theorem fr_noWrap (hpre : OpenPhasePre P R Q m0) {o n : Nat} (hon : o + n ≤ 176) :
    NoWrap (base m0 176 + BitVec.ofNat 64 o) n := by
  have hl := m0.regs.SP.toNat_lt
  have h1 := hN hpre
  rw [openPhaseStack_eq] at h1
  unfold NoWrap
  rw [fr_toNat hpre (o := o) (by omega)]
  omega

theorem fr_mapped (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 m) {o n : Nat}
    (hon : o + n ≤ 176) : Mapped m.dmem (base m0 176 + BitVec.ofNat 64 o) n := by
  intro i hi
  rw [NativeRustcVm.addr_add_add]
  exact hf.kept _ ((Bus.frame_mapped hpre.1 (by decide)).1 _ (by omega))

/-- The frame's bytes, apart from a callee's stack. -/
theorem fr_apart_callee (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 m) {o n N' : Nat}
    (hon : o + n ≤ 176) (hle : 176 + N' ≤ openPhaseStack) :
    Apart (base m0 176 + BitVec.ofNat 64 o) n (stackBelow m N') N' := by
  have h1 := hN hpre
  rw [openPhaseStack_eq] at h1 hle
  rw [stackBelow_eq hf.sp (N' := N') (by omega)]
  have hb := base_toNat (m0 := m0) (F := 176 + N') (by omega)
  have e := fr_toNat hpre (o := o) (by omega)
  unfold Apart
  rw [hb, e]
  omega

/-- **After a call from the frame** that writes 32 bytes of the frame at `o`, below the slots,
and its stack: the frame, and the frame's other bytes kept. -/
theorem afterCall (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 m) {m' : MachineData}
    {N' o : Nat} (hle : 176 + N' ≤ openPhaseStack) (ho : o + 32 ≤ 80) (hS : Saved m m')
    (hs : SameOutside m.dmem m'.dmem fun q ↦
      InRange (base m0 176 + BitVec.ofNat 64 o) 32 q ∨ InRange (stackBelow m N') N' q) :
    FrO m0 m' ∧ ∀ {o' : Nat} {bs : List UInt8}, o' + bs.length ≤ 176 →
      (o' + bs.length ≤ o ∨ o + 32 ≤ o') →
      NativeRustcVm.BytesAt m.dmem (base m0 176 + BitVec.ofNat 64 o') bs →
      NativeRustcVm.BytesAt m'.dmem (base m0 176 + BitVec.ofNat 64 o') bs := by
  have hsl : ∀ p ∈ slotsO, 80 ≤ p.1 ∧ p.1 + 8 ≤ 176 := by decide
  refine ⟨frCallLocal hf (hN hpre) hle (o := o) (w := 32) (by omega) (fun r hr ↦ nomatch hr)
    (fun p hp ↦ ⟨by have := hsl p hp; omega, (hsl p hp).2⟩) (outs' := fun _ ↦ False)
    (fun _ h ↦ h) (fun _ h ↦ h.elim) hS
    (NativeRustcVm.SameOutside.mono hs fun q hq ↦ hq.elim .inl fun h ↦ .inr (.inr h)), ?_⟩
  intro o' bs hob hd h
  have h1 := hN hpre
  rw [openPhaseStack_eq] at h1 hle
  have hl := m0.regs.SP.toNat_lt
  have hb := base_toNat (m0 := m0) (F := 176) (by omega)
  have hb' := base_toNat (m0 := m0) (F := 176 + N') (by omega)
  refine NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hq ↦ ?_
  have e : (base m0 176 + BitVec.ofNat 64 o' + BitVec.ofNat 64 i).toNat =
      m0.regs.SP.toNat - 176 + (o' + i) := by
    rw [NativeRustcVm.addr_add_add, fr_toNat hpre (o := o' + i) (by omega)]
  rcases hq with hq | hq
  · rw [Sym.inRange_iff (fr_noWrap hpre (n := 32) (o := o) (by omega)),
      fr_toNat hpre (o := o) (by omega), e] at hq
    omega
  · rw [stackBelow_eq hf.sp (N' := N') (by omega),
      Sym.inRange_iff (NativeRustcVm.NoWrap.mono
        (base_noWrap (m0 := m0) (F := 176 + N') (by omega)) (by omega : N' ≤ 176 + N')),
      hb', e] at hq
    omega

/-- **The climbs' invariant kept** by a step keeping the callee-saved registers and the frame's
first 16 bytes. -/
theorem CInv.keep {h w j : Nat} (hi : CInv m0 P Q R h w j m) {m' : MachineData}
    (hf : FrO m0 m') (hr : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r)
    (hd : ∀ {o' : Nat} {bs : List UInt8}, o' + bs.length ≤ 16 →
      NativeRustcVm.BytesAt m.dmem (base m0 176 + BitVec.ofNat 64 o') bs →
      NativeRustcVm.BytesAt m'.dmem (base m0 176 + BitVec.ofNat 64 o') bs) :
    CInv m0 P Q R h w j m' :=
  ⟨hf, hi.lt, (hr .X19 rfl).trans hi.x19, by rw [hr .X20 rfl]; exact hi.x20,
    (hr .X21 rfl).trans hi.x21, (hr .X22 rfl).trans hi.x22, (hr .X23 rfl).trans hi.x23,
    by rw [hr .X24 rfl]; exact hi.x24, by rw [hr .X25 rfl]; exact hi.x25,
    (hr .X26 rfl).trans hi.x26, (hr .X27 rfl).trans hi.x27, (hr .X28 rfl).trans hi.x28,
    (hr .X29 rfl).trans hi.x29, hd (by simp [NativeRustcVm.length_wordBytes]) hi.w0,
    hd (by simp [NativeRustcVm.length_wordBytes]) hi.w8, hi.shape, hi.pos, hi.climbs⟩

end

end NativeRustcVmArm.Sumcheck.OpenPhase
