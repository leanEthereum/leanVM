import Rv64Verifier.Proofs.Transcript.RoundPolyCall

/-!
# `sumcheck_round_poly`'s `Some` path, to its tail

`0x8000c370`: `next_scalars(count - 1)` into `S - 152`; its `Err` to the result (`0x8000c5c8`),
its `Vec` in `s6`, `s5`, `s4` (`TailS`).
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem mirror_some {s : MachineState} (htag : s.getMem (s.getReg .x14) ≠ 0) (T : TState) :
    (mirror s).run T = ((TM.nextScalars ((s.getReg .x12).toNat - 1)).run T).bind fun r ↦
      some ([eAt s (s.getReg .x13) + eAt s (s.getReg .x14 + 8) * sumE r.1] ++ r.1, r.2) := by
  rw [mirror, show optEAt s (s.getReg .x14) = some (eAt s (s.getReg .x14 + 8)) by
    simp only [optEAt, ite_eq_right htag], roundPoly_some_run]

/-- At `0x8000c398`: the tail's `Vec` (capacity `s6`, buffer `s5`, length `s4`), what the mirror
reads so far. -/
structure TailS (s v : MachineState) : Prop where
  fr : Fr s v
  x18 : v.getReg .x18 = s.getReg .x13
  x19 : v.getReg .x19 = s.getReg .x14
  room : (v.getReg .x20).toNat ≤ (v.getReg .x22).toNat
  buf : NewBuf s v (v.getReg .x21) ((v.getReg .x22).toNat * 24) 8
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ T',
    (TM.nextScalars ((s.getReg .x12).toNat - 1)).run T =
      some (eListAt v (v.getReg .x21) (v.getReg .x20).toNat, T') ∧
      TranscriptAt v (s.getReg .x11) T'

set_option maxHeartbeats 1000000 in
theorem someTail (hNS : NextScalarsSpec) {s u : MachineState} (hpre : RoundPolyPre s)
    (hpc : u.pc = 0x8000c370) (h : Fr s u) (x18 : u.getReg .x18 = s.getReg .x13)
    (kr : ∀ r ∈ [Reg.x11, .x12, .x14], u.getReg r = s.getReg r)
    (htag : s.getMem (s.getReg .x14) ≠ 0)
    (hT : ∀ T, TranscriptAt s (s.getReg .x11) T → TranscriptAt u (s.getReg .x11) T) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x8000c398 ∧ TailS s v) ∨ Done s v) := by
  have hb := bounds hpre
  have hS : 80 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c370_spec hpc trivial
  have k₁ := b8000c370_keeps h₁
  have hm₁ := b8000c370_mem_same h₁
  have F₁ : Fr s c := h.same hS (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁
  have x10₁ : c.getReg .x10 = s.getReg .x2 - 152 := by
    rw [b8000c370_x10 h₁, h.saved.x2]; ring
  have x11₁ : c.getReg .x11 = s.getReg .x11 := (k₁ .x11 (by decide)).trans (kr .x11 (by simp))
  have x12₁ : (c.getReg .x12).toNat = (s.getReg .x12).toNat - 1 := by
    have := hpre.count
    rw [b8000c370_x12 h₁, kr .x12 (by simp), AddrOmega.sub_le _ _ (by simp only [Sym.wordToNatLit]; omega)]
    rfl
  have hTc (T : TState) (hTs : TranscriptAt s (s.getReg .x11) T) : TranscriptAt c (s.getReg .x11) T :=
    Fr.transcriptAt hpre h F₁.heap.hi (DFrame.of_same hm₁ _) (hT T hTs)
  obtain ⟨t, hr₂, ⟨hpc₂, O⟩ | hd⟩ := call_ns hNS hpre F₁ (b8000c370_pc h₁) x10₁ x11₁
  swap
  · exact ⟨t, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  have x2₂ : t.getReg .x2 = s.getReg .x2 - 160 := O.fr.saved.x2
  obtain ⟨t₁, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c384_spec
    (by rw [hpc₂, returnAddress_eq, b8000c370_x1 h₁]; decide) (by
      rv_eval [x2₂]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000c384_keeps h₃
  have hm₃ := b8000c384_mem_same h₃
  have F₃ : Fr s t₁ := O.fr.same hS (fun r hr ↦ k₃ r (mem_of_mem hr _)) hm₃
  have x22₃ : t₁.getReg .x22 = vecCap t (s.getReg .x2 - 152) := by
    rw [b8000c384_x22 h₃, x2₂, show s.getReg .x2 - 160 + 8 = s.getReg .x2 - 152 by ring]; rfl
  have x21₃ : t₁.getReg .x21 = vecPtr t (s.getReg .x2 - 152) := by
    rw [b8000c384_x21 h₃, x2₂, show s.getReg .x2 - 160 + 16 = s.getReg .x2 - 152 + 8 by ring]; rfl
  have x20₃ : t₁.getReg .x20 = vecLen t (s.getReg .x2 - 152) := by
    rw [b8000c384_x20 h₃, x2₂, show s.getReg .x2 - 160 + 24 = s.getReg .x2 - 152 + 16 by ring]; rfl
  by_cases hc : vecCap t (s.getReg .x2 - 152) = errNiche
  · -- `Err` from `next_scalars`
    have x8₃ := F₃.x8
    have ho := hpre.out
    obtain ⟨t₂, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c5c8_spec
      (b8000c384_pc_taken h₃ (by
        rw [x2₂, show s.getReg .x2 - 160 + 8 = s.getReg .x2 - 152 by ring]; exact hc)) (by
      rv_eval [x8₃]
      and_intros <;> (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f := b8000c5c8_frame h₄ (by rw [x8₃]; addr_omega [ho])
    have m0 := b8000c5c8_m_x8_0 h₄
    have m8 := b8000c5c8_m_x8_8 h₄
    rw [x8₃] at f m0 m8
    have E := ErrState.of_write hpre F₃ (fun r hr ↦ b8000c5c8_keeps h₄ r (mem_of_mem hr _)) f
      (by rw [m0, b8000c384_x10 h₃]; rfl) (by rw [m8, x21₃]; exact O.err hc) fun T hTs ↦ by
        have v := O.value T (hTc T hTs)
        rw [x12₁] at v
        rw [mirror_some htag]
        revert v
        cases (TM.nextScalars ((s.getReg .x12).toNat - 1)).run T with
        | none => intro _; rfl
        | some p => intro v; exact absurd hc v.1
    obtain ⟨t', hr', pc', pres', post'⟩ := exitErr hpre (b8000c5c8_pc h₄) E
    exact ⟨t', hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr'))), Or.inr (Or.inl ⟨pc', pres', post'⟩)⟩
  -- `Ok`
  obtain ⟨hvec, hnb⟩ := O.ok hc
  have nx₃ : heapNext t₁ = heapNext t := by simp only [heapNext, hm₃]
  have mc := F₁.mono
  refine ⟨t₁, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨b8000c384_pc_not_taken h₃ (by
    rw [x2₂, show s.getReg .x2 - 160 + 8 = s.getReg .x2 - 152 by ring]; exact hc), {
    fr := F₃
    x18 := by
      rw [k₃ .x18 (by decide), O.pres.reg .x18, k₁ .x18 (by decide), x18]
    x19 := by
      rw [k₃ .x19 (by decide), O.pres.reg .x19, b8000c370_x19 h₁, kr .x14 (by simp)]
    room := by rw [x20₃, x22₃]; exact hvec.len
    buf := by
      rw [x21₃, x22₃]
      simp only [NewBuf, nx₃] at hnb ⊢
      omega
    value := fun T hTs ↦ by
      have v := O.value T (hTc T hTs)
      rw [x12₁] at v
      revert v
      cases (TM.nextScalars ((s.getReg .x12).toNat - 1)).run T with
      | none => intro v; exact absurd v hc
      | some p =>
        obtain ⟨xs, T'⟩ := p
        intro v
        obtain ⟨-, hnv, hT'⟩ := v
        refine ⟨T', ?_, Fr.transcriptAt hpre O.fr F₃.heap.hi (DFrame.of_same hm₃ _) hT'⟩
        rw [← hnv.elems, x21₃, x20₃]
        simp only [vecEs]
        rw [(DFrame.of_same hm₃ fun _ ↦ False).eListAt fun _ _ h ↦ h] }⟩⟩

end Rv64Verifier.Transcript.RoundPoly
