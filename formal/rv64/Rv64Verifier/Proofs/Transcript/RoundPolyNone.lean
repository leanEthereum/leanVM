import Rv64Verifier.Proofs.Transcript.RoundPolyCall

/-!
# `sumcheck_round_poly`'s `None` path, to its tail

`0x8000c488`: `next_scalar` into `S - 152` (`noneConst`), its `Err` to the result (`0x8000c4ac`);
`next_scalars(count - 2)` into `S - 152` (`noneTail`), its `Err` to the result (`0x8000c5d8`), its
`Vec` in `s7`, `s5`, `s1`, the constant's limbs in `s4`, `s3`, `s6` (`TailN`).
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem mirror_none {s : MachineState} (htag : s.getMem (s.getReg .x14) = 0) (T : TState) :
    (mirror s).run T = (TM.nextScalar.run T).bind fun p ↦
      ((TM.nextScalars ((s.getReg .x12).toNat - 2)).run p.2).bind fun r ↦
        some ([p.1, eAt s (s.getReg .x13) + sumE r.1] ++ r.1, r.2) := by
  rw [mirror, show optEAt s (s.getReg .x14) = none by simp only [optEAt, htag, ↓reduceIte],
    roundPoly_none_run]

/-- At `0x8000c4c0`: the constant at `S - 144`, its low limbs in `s4`, `s3`. -/
structure ConstN (s v : MachineState) : Prop where
  fr : Fr s v
  x9 : v.getReg .x9 = s.getReg .x11
  x18 : v.getReg .x18 = s.getReg .x13
  x21 : v.getReg .x21 = s.getReg .x12
  x20 : v.getReg .x20 = v.getMem (s.getReg .x2 - 144)
  x19 : v.getReg .x19 = v.getMem (s.getReg .x2 - 136)
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ T₁,
    TM.nextScalar.run T = some (eAt v (s.getReg .x2 - 144), T₁) ∧ TranscriptAt v (s.getReg .x11) T₁

set_option maxHeartbeats 2000000 in
theorem noneConst (hN : NextScalarSpec) {s u : MachineState} (hpre : RoundPolyPre s)
    (hpc : u.pc = 0x8000c488) (h : Fr s u) (x18 : u.getReg .x18 = s.getReg .x13)
    (kr : ∀ r ∈ [Reg.x11, .x12, .x14], u.getReg r = s.getReg r)
    (htag : s.getMem (s.getReg .x14) = 0)
    (hT : ∀ T, TranscriptAt s (s.getReg .x11) T → TranscriptAt u (s.getReg .x11) T) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x8000c4c0 ∧ ConstN s v) ∨ Done s v) := by
  have hb := bounds hpre
  have hS : 80 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hself := hpre.selfStack
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c488_spec hpc trivial
  have k₁ := b8000c488_keeps h₁
  have hm₁ := b8000c488_mem_same h₁
  have F₁ : Fr s c := h.same hS (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁
  have x2 := F₁.saved.x2
  have x10₁ : c.getReg .x10 = s.getReg .x2 - 152 := by
    rw [b8000c488_x10 h₁, h.saved.x2]; ring
  have x11₁ : c.getReg .x11 = s.getReg .x11 := (k₁ .x11 (by decide)).trans (kr .x11 (by simp))
  have hTc (T : TState) (hTs : TranscriptAt s (s.getReg .x11) T) : TranscriptAt c (s.getReg .x11) T :=
    Fr.transcriptAt hpre h F₁.heap.hi (DFrame.of_same hm₁ _) (hT T hTs)
  have tp : TPre 32 nextScalarStack c := TPre.callee 160 hpre.toTPre F₁.heap F₁.mono
    (F₁.frame.mono fun _ h ↦ h.toW) (by rw [x2]; rfl) x11₁ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [x10₁]; refine ⟨?_, ?_, ?_⟩ <;> addr_omega [hb])
  have hnp : NextScalarPre c := {
    out := tp.out, self := tp.self, stack := tp.stack, outStack := tp.outStack,
    selfStack := tp.selfStack, outSelf := tp.outSelf, proofStack := tp.proofStack,
    proofOut := tp.proofOut, rodata := tp.rodata, outRodata := tp.outRodata,
    selfRodata := tp.selfRodata }
  obtain ⟨t, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hN.call hr₁ (b8000c488_pc h₁) hnp
  swap
  · exact ⟨t, hr₂, Or.inr (Or.inr hd)⟩
  have G := hpost₂.frame
  simp only [stackLo, x2, x10₁, x11₁] at G
  have hmt (y : Word) (h0 : ∀ i < 8, ¬ (Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 152) 32 ∨
      Within (y + BitVec.ofNat 64 i) (s.getReg .x11 + 8) 344 ∨
      Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 160 - BitVec.ofNat 64 nextScalarStack)
        nextScalarStack)) : t.getMem y = c.getMem y := G y h0
  have nxt : heapNext t = heapNext c := by
    simp only [heapNext]
    rw [hmt _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb, hst.next, hself, hpre.self.self,
        hpre.selfFree]]
  have Ft : Fr s t := {
    saved := F₁.saved.step hS (hpres₂.reg .x2) (fun r hr ↦ hpres₂ r (by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide))
      fun y h1 h2 ↦ hmt y fun i hi hw ↦ by
        rcases hw with hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hb, hself, hpre.self.self]
    x8 := (hpres₂.reg .x8).trans F₁.x8
    heap := ⟨by rw [nxt]; exact F₁.heap.lo, by rw [nxt]; exact F₁.heap.hi⟩
    mono := by rw [nxt]; exact F₁.mono
    frame := (F₁.frame.mono fun a h ↦ V.mono (Nat.le_of_eq nxt.symm) h).trans G fun a hw ↦ by
      rcases hw with hw | hw | hw
      · exact Or.inr (Or.inl (by addr_omega [hw, hb]))
      · exact Or.inl hw
      · exact Or.inr (Or.inl (by addr_omega [hw, hb])) }
  have x2t : t.getReg .x2 = s.getReg .x2 - 160 := Ft.saved.x2
  obtain ⟨t₁, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c49c_spec
    (by rw [hpc₂, returnAddress_eq, b8000c488_x1 h₁]; decide) (by
      rv_eval [x2t]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000c49c_keeps h₃
  have hm₃ := b8000c49c_mem_same h₃
  have F₃ : Fr s t₁ := Ft.same hS (fun r hr ↦ k₃ r (mem_of_mem hr _)) hm₃
  have e8 : s.getReg .x2 - 160 + 8 = s.getReg .x2 - 152 := by ring
  have val := hpost₂.value
  have err := hpost₂.err
  rw [x10₁, x11₁] at val
  rw [x10₁] at err
  by_cases hc : t.getMem (s.getReg .x2 - 152) = 0
  swap
  · -- `Err` from `next_scalar`
    have x8₃ := F₃.x8
    have ho := hpre.out
    obtain ⟨t₂, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c4ac_spec
      (b8000c49c_pc_not_taken h₃ (by rw [x2t, e8]; exact hc)) (by
      rv_eval [x8₃]
      and_intros <;> (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f := b8000c4ac_frame h₄ (by rw [x8₃]; addr_omega [ho])
    have m0 := b8000c4ac_m_x8_0 h₄
    have m8 := b8000c4ac_m_x8_8 h₄
    rw [x8₃] at f m0 m8
    have E := ErrState.of_write hpre F₃ (fun r hr ↦ b8000c4ac_keeps h₄ r (mem_of_mem hr _)) f
      (by rw [m0]; rfl) (by
        rw [m8, b8000c49c_x20 h₃, x2t, show s.getReg .x2 - 160 + 16 = s.getReg .x2 - 152 + 8 by ring,
          err hc]
        decide) fun T hTs ↦ by
        have v := val T (hTc T hTs)
        rw [mirror_none htag]
        revert v
        cases TM.nextScalar.run T with
        | none => intro _; rfl
        | some p => intro v; exact absurd v.1 hc
    obtain ⟨t', hr', pc', pres', post'⟩ := exitErr hpre (b8000c4ac_pc h₄) E
    exact ⟨t', hr₂.trans (hr₃.trans (hr₄.trans hr')), Or.inr (Or.inl ⟨pc', pres', post'⟩)⟩
  refine ⟨t₁, hr₂.trans hr₃, Or.inl ⟨b8000c49c_pc_taken h₃ (by rw [x2t, e8]; exact hc), {
    fr := F₃
    x9 := by rw [k₃ .x9 (by decide), hpres₂.reg .x9, b8000c488_x9 h₁, kr .x11 (by simp)]
    x18 := by rw [k₃ .x18 (by decide), hpres₂.reg .x18, k₁ .x18 (by decide), x18]
    x21 := by rw [k₃ .x21 (by decide), hpres₂.reg .x21, b8000c488_x21 h₁, kr .x12 (by simp)]
    x20 := by
      rw [b8000c49c_x20 h₃, x2t, hm₃, show s.getReg .x2 - 160 + 16 = s.getReg .x2 - 144 by ring]
    x19 := by
      rw [b8000c49c_x19 h₃, x2t, hm₃, show s.getReg .x2 - 160 + 24 = s.getReg .x2 - 136 by ring]
    value := fun T hTs ↦ by
      have v := val T (hTc T hTs)
      revert v
      cases TM.nextScalar.run T with
      | none => intro v; exact absurd v.1 (by rw [hc]; decide)
      | some p =>
        obtain ⟨x, T₁⟩ := p
        intro v
        obtain ⟨-, hx, hT₁⟩ := v
        refine ⟨T₁, ?_, Fr.transcriptAt hpre Ft F₃.heap.hi (DFrame.of_same hm₃ _) hT₁⟩
        rw [show s.getReg .x2 - 144 = s.getReg .x2 - 152 + 8 by ring,
          (DFrame.of_same hm₃ fun _ ↦ False).eAt fun _ _ h ↦ h, hx] }⟩⟩

end Rv64Verifier.Transcript.RoundPoly
