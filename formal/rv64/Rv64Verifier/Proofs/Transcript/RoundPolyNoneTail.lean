import Rv64Verifier.Proofs.Transcript.RoundPolyNone

/-!
# `sumcheck_round_poly`'s `None` path: `next_scalars(count - 2)`
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- At `0x8000c4ec`: the constant's limbs in `s4`, `s3`, `s6`, the tail's `Vec` (capacity `s7`,
buffer `s5`, length `s1`), what the mirror reads so far. -/
structure TailN (s v : MachineState) : Prop where
  fr : Fr s v
  x18 : v.getReg .x18 = s.getReg .x13
  room : (v.getReg .x9).toNat ≤ (v.getReg .x23).toNat
  buf : NewBuf s v (v.getReg .x21) ((v.getReg .x23).toNat * 24) 8
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ x T₁ T',
    TM.nextScalar.run T = some (x, T₁) ∧
    Model.limbs x = (v.getReg .x20, v.getReg .x19, v.getReg .x22) ∧
    (TM.nextScalars ((s.getReg .x12).toNat - 2)).run T₁ =
      some (eListAt v (v.getReg .x21) (v.getReg .x9).toNat, T') ∧
    TranscriptAt v (s.getReg .x11) T'

set_option maxHeartbeats 2000000 in
theorem noneTail (hNS : NextScalarsSpec) {s v : MachineState} (hpre : RoundPolyPre s)
    (htag : s.getMem (s.getReg .x14) = 0) (hpc : v.pc = 0x8000c4c0) (h : ConstN s v) :
    ∃ w, Reaches Image.code v w ∧ ((w.pc = 0x8000c4ec ∧ TailN s w) ∨ Done s w) := by
  have hb := bounds hpre
  have hS : 80 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have x2v := h.fr.saved.x2
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c4c0_spec hpc (by
    rv_eval [x2v]
    valid_access hpre.stack.valid [hb])
  have k₁ := b8000c4c0_keeps h₁
  have hm₁ := b8000c4c0_mem_same h₁
  have F₁ : Fr s c := h.fr.same hS (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁
  have x10₁ : c.getReg .x10 = s.getReg .x2 - 152 := by
    rw [b8000c4c0_x10 h₁, x2v]; ring
  have x11₁ : c.getReg .x11 = s.getReg .x11 := by rw [b8000c4c0_x11 h₁, h.x9]
  have x12₁ : (c.getReg .x12).toNat = (s.getReg .x12).toNat - 2 := by
    have := hpre.count
    rw [b8000c4c0_x12 h₁, h.x21, AddrOmega.sub_le _ _ (by simp only [Sym.wordToNatLit]; omega)]
    rfl
  have x22₁ : c.getReg .x22 = v.getMem (s.getReg .x2 - 128) := by
    rw [b8000c4c0_x22 h₁, x2v, show s.getReg .x2 - 160 + 32 = s.getReg .x2 - 128 by ring]
  obtain ⟨t, hr₂, ⟨hpc₂, O⟩ | hd⟩ := call_ns hNS hpre F₁ (b8000c4c0_pc h₁) x10₁ x11₁
  swap
  · exact ⟨t, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  have x2₂ : t.getReg .x2 = s.getReg .x2 - 160 := O.fr.saved.x2
  obtain ⟨t₁, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c4d8_spec
    (by rw [hpc₂, returnAddress_eq, b8000c4c0_x1 h₁]; decide) (by
      rv_eval [x2₂]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000c4d8_keeps h₃
  have hm₃ := b8000c4d8_mem_same h₃
  have F₃ : Fr s t₁ := O.fr.same hS (fun r hr ↦ k₃ r (mem_of_mem hr _)) hm₃
  have x23₃ : t₁.getReg .x23 = vecCap t (s.getReg .x2 - 152) := by
    rw [b8000c4d8_x23 h₃, x2₂, show s.getReg .x2 - 160 + 8 = s.getReg .x2 - 152 by ring]; rfl
  have x21₃ : t₁.getReg .x21 = vecPtr t (s.getReg .x2 - 152) := by
    rw [b8000c4d8_x21 h₃, x2₂, show s.getReg .x2 - 160 + 16 = s.getReg .x2 - 152 + 8 by ring]; rfl
  have x9₃ : t₁.getReg .x9 = vecLen t (s.getReg .x2 - 152) := by
    rw [b8000c4d8_x9 h₃, x2₂, show s.getReg .x2 - 160 + 24 = s.getReg .x2 - 152 + 16 by ring]; rfl
  have hTc (T₁ : TState) (hT₁ : TranscriptAt v (s.getReg .x11) T₁) :
      TranscriptAt c (s.getReg .x11) T₁ :=
    Fr.transcriptAt hpre h.fr F₁.heap.hi (DFrame.of_same hm₁ _) hT₁
  by_cases hc : vecCap t (s.getReg .x2 - 152) = errNiche
  · -- `Err` from `next_scalars`
    have x8₃ := F₃.x8
    have ho := hpre.out
    obtain ⟨t₂, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c5d8_spec
      (b8000c4d8_pc_taken h₃ (by
        rw [x2₂, show s.getReg .x2 - 160 + 8 = s.getReg .x2 - 152 by ring]; exact hc)) (by
      rv_eval [x8₃]
      and_intros <;> (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f := b8000c5d8_frame h₄ (by rw [x8₃]; addr_omega [ho])
    have m0 := b8000c5d8_m_x8_0 h₄
    have m8 := b8000c5d8_m_x8_8 h₄
    rw [x8₃] at f m0 m8
    have E := ErrState.of_write hpre F₃ (fun r hr ↦ b8000c5d8_keeps h₄ r (mem_of_mem hr _)) f
      (by rw [m0, b8000c4d8_x10 h₃]; rfl) (by rw [m8, x21₃]; exact O.err hc) fun T hTs ↦ by
        obtain ⟨T₁, h1, h2⟩ := h.value T hTs
        have w := O.value T₁ (hTc T₁ h2)
        rw [x12₁] at w
        rw [mirror_none htag, h1]
        simp only [Option.bind_some]
        revert w
        cases (TM.nextScalars ((s.getReg .x12).toNat - 2)).run T₁ with
        | none => intro _; rfl
        | some p => intro w; exact absurd hc w.1
    obtain ⟨t', hr', pc', pres', post'⟩ := exitErr hpre (b8000c5d8_pc h₄) E
    exact ⟨t', hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr'))), Or.inr (Or.inl ⟨pc', pres', post'⟩)⟩
  -- `Ok`
  obtain ⟨hvec, hnb⟩ := O.ok hc
  have nx₃ : heapNext t₁ = heapNext t := by simp only [heapNext, hm₃]
  have mc := F₁.mono
  have kc (r : Reg) (hr : r ∈ [Reg.x19, .x20]) : t₁.getReg r = v.getReg r := by
    rw [k₃ r (mem_of_mem hr _), O.pres r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x22₃ : t₁.getReg .x22 = v.getMem (s.getReg .x2 - 128) := by
    rw [k₃ .x22 (by decide), O.pres.reg .x22, x22₁]
  refine ⟨t₁, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨b8000c4d8_pc_not_taken h₃ (by
    rw [x2₂, show s.getReg .x2 - 160 + 8 = s.getReg .x2 - 152 by ring]; exact hc), {
    fr := F₃
    x18 := by rw [k₃ .x18 (by decide), O.pres.reg .x18, k₁ .x18 (by decide), h.x18]
    room := by rw [x9₃, x23₃]; exact hvec.len
    buf := by
      rw [x21₃, x23₃]
      simp only [NewBuf, nx₃] at hnb ⊢
      omega
    value := fun T hTs ↦ by
      obtain ⟨T₁, h1, h2⟩ := h.value T hTs
      have w := O.value T₁ (hTc T₁ h2)
      rw [x12₁] at w
      cases hns : (TM.nextScalars ((s.getReg .x12).toNat - 2)).run T₁ with
      | none => rw [hns] at w; exact absurd w hc
      | some p =>
        obtain ⟨xs, T'⟩ := p
        rw [hns] at w
        obtain ⟨-, hnv, hT'⟩ := w
        refine ⟨_, T₁, T', h1, ?_, ?_, Fr.transcriptAt hpre O.fr F₃.heap.hi (DFrame.of_same hm₃ _) hT'⟩
        · rw [limbs_eAt, kc .x20 (by simp), kc .x19 (by simp), x22₃, h.x20, h.x19,
            show s.getReg .x2 - 144 + 8 = s.getReg .x2 - 136 by ring,
            show s.getReg .x2 - 144 + 16 = s.getReg .x2 - 128 by ring]
        · rw [hns, ← hnv.elems, x21₃, x9₃, vecEs, (DFrame.of_same hm₃ fun _ ↦ False).eListAt
            fun _ _ h ↦ h] }⟩⟩

end Rv64Verifier.Transcript.RoundPoly
