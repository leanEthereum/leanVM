import Rv64Verifier.Proofs.Bytecode.EvalCalled

/-!
# `Bytecode::evaluate`: into the loop

`0x80010efc` branches on `self.blocks.len()`: to the empty table's `Ok(ZERO)` (`EmptyOk`), or on to
`0x80010f04`, which caches the `Bytecode`'s fields and the buffers on the stack and enters the loop
(`EnvOk`, `InitRegs`).
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

set_option maxHeartbeats 4000000 in
theorem enter {s u : MachineState} {low high bk : Word} (hpre : EvaluatePre s)
    (hpc : u.pc = 0x80010efc) (hc : Called s u low high bk) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x800116ec ∧ EmptyOk s v) ∨
      (v.pc = 0x80011090 ∧ EnvOk ⟨s, v, low, high, bk⟩ ∧ InitRegs ⟨s, v, low, high, bk⟩ v)) := by
  have hsp := sp_bounds hpre.stack
  have hstn := hpre.stack.next
  have hstr := hpre.stack.rodata
  have hbc := hpre.bc.self
  have hbca := hpre.bc.align
  have hbcc := hpre.bcClear.self
  have hhi := hc.heap.hi
  have hmono := hc.mono
  simp only [heapNext, heapEnd] at hhi hmono
  have e2 : u.getReg .x2 = s.getReg .x2 - 1968 := hc.saved.sp
  -- the `Bytecode`'s doublewords are the entry's
  have rbc (a : Word) (h1 : (s.getReg .x11).toNat ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x11).toNat + 136) : u.getMem a = s.getMem a :=
    hc.frame a fun i hi hw ↦ by
      simp only [Fresh, heapNext] at hw
      addr_omega [hw, h1, h2, hi, hbc, hbcc, hsp, hhi, hmono]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010efc_spec hpc (by
    rv_eval [hc.x8]
    valid_in hbc [hbc, hbca])
  have k₁ := b80010efc_keeps h₁
  have hm₁ := b80010efc_mem_same h₁
  have hlen : u.getMem (u.getReg .x8 + 16) = vecLen s (s.getReg .x11) := by
    rw [hc.x8, rbc _ (by addr_omega [hbc]) (by addr_omega [hbc])]; rfl
  by_cases h0 : vecLen s (s.getReg .x11) = 0
  · refine ⟨u₁, hr₁, Or.inl ⟨b80010efc_pc_taken h₁ (by rw [hlen, h0]), ?_⟩⟩
    exact {
      saved := hc.saved.of_frame (k₁ .x2 (by decide)) (fun a _ _ ↦ hm₁ a) (by addr_omega [hsp])
      out := by rw [hm₁, hc.out]
      heap := ⟨by simp only [heapNext, hm₁]; exact hc.heap.lo, by simp only [heapNext, hm₁]; exact hc.heap.hi⟩
      mono := by simp only [heapNext, hm₁]; exact hc.mono
      frame := (hc.frame.trans (Transcript.DFrame.of_same hm₁ fun _ ↦ False) fun _ h ↦ h.elim).mono
        fun a h ↦ by simp only [Fresh, heapNext, hm₁] at h ⊢; exact h
      short := hc.short
      len := hc.len
      empty := h0 }
  have e2₁ : u₁.getReg .x2 = s.getReg .x2 - 1968 := (k₁ .x2 (by decide)).trans e2
  have e8₁ : u₁.getReg .x8 = s.getReg .x11 := (k₁ .x8 (by decide)).trans hc.x8
  have hst := hpre.stack.valid
  have hbcm := hpre.bc.self
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80010f04_spec (b80010efc_pc_not_taken h₁ (by
    rw [hlen]; exact h0)) (by
      rv_eval [e2₁, e8₁]
      and_intros <;> first
        | valid_access hst [hsp]
        | valid_in hbc [hbc, hbca]
        | addr_omega [hsp, hbc, hbcc])
  have k₂ := b80010f04_keeps h₂
  have hfr : ∀ a, ¬ Within a (s.getReg .x2 - 1952) 160 → u₂.getMem a = u.getMem a := fun a ha ↦ by
    rw [h₂.frame a (by rv_eval [e2₁, e8₁]; and_intros <;> addr_omega [ha, hsp]), hm₁]
  have hfs (a : Word) (ha : a = s.getReg .x2 - 1912 ∨ a = s.getReg .x2 - 1904) :
      u₂.getMem a = u.getMem a := by
    rw [h₂.frame a (by rv_eval [e2₁, e8₁]; rcases ha with rfl | rfl <;> and_intros <;>
      addr_omega [hsp]), hm₁]
  have rd (k : Word) (hk : 8 ≤ k.toNat ∧ k.toNat + 8 ≤ 136) :
      u₁.getMem (s.getReg .x11 + k) = s.getMem (s.getReg .x11 + k) := by
    rw [hm₁, rbc _ (by addr_omega [hbc, hk]) (by addr_omega [hbc, hk])]
  have hnext₂ : u₂.getMem nextAddr = u.getMem nextAddr := hfr _ (by addr_omega [hsp, hstn])
  have u₂f := h₂.unaligned (by rv_eval [e2₁]; and_intros <;> addr_omega [hsp])
  have bf₂ : ByteFrame u₁ u₂ (Within · (s.getReg .x2 - 1952) 160) :=
    ByteFrame.of_memFrame (fun a ha ↦ by rw [hfr a ha, hm₁]) (by addr_omega [hsp]) (by decide) u₂f
  have m16 := b80010f04_m_x2_16 h₂
  have m24 := b80010f04_m_x2_24 h₂
  have m32 := b80010f04_m_x2_32 h₂
  have m40 := b80010f04_m_x2_40 h₂
  have m48 := b80010f04_m_x2_48 h₂
  have m128 := b80010f04_m_x2_128 h₂
  have m136 := b80010f04_m_x2_136 h₂
  have m144 := b80010f04_m_x2_144 h₂
  have m152 := b80010f04_m_x2_152 h₂
  have m160 := b80010f04_m_x2_160 h₂
  have m168 := b80010f04_m_x2_168 h₂
  simp only [e2₁, e8₁] at m16 m24 m32 m40 m48 m128 m136 m144 m152 m160 m168
  rv_eval [] at m16 m24 m32 m40 m48 m128 m136 m144 m152 m160 m168
  have x10₁ : u₁.getReg .x10 = vecLen s (s.getReg .x11) := by rw [b80010efc_x10 h₁, hlen]
  refine ⟨u₂, hr₁.trans hr₂, Or.inr ⟨b80010f04_pc h₂, ?_, ?_⟩⟩
  · exact {
      pre := hpre
      rodataL := RodataOk.of_byteFrame (RodataOk.of_dwords hc.rodata fun a _ ↦ hm₁ a) bf₂
        fun a ha hw ↦ by addr_omega [ha, hw, hsp, hpre.stack.rodata]
      short := hc.short
      len := hc.len
      saved := hc.saved.of_frame ((k₂ .x2 (by decide)).trans (k₁ .x2 (by decide)))
        (fun a h1 h2 ↦ by rw [hfr a (by addr_omega [h1, h2, hsp]), ← hm₁ a])
        (by addr_omega [hsp])
      out := by rw [hfr _ (by addr_omega [hsp])]; exact hc.out
      c16 := by
        rw [m16, rd 80 (by decide)]
        simp only [Env.bytesPtr, Env.bcp, vecPtr]
        rv_eval []
      c24 := by
        rw [m24, rd 32 (by decide)]
        simp only [Env.wordsPtr, Env.bcp, vecPtr]
        rv_eval []
      c32 := by rw [m32, x10₁, rd 8 (by decide)]; rfl
      c40 := by
        rw [m40, rd 88 (by decide)]
        simp only [Env.bytesLen, Env.bcp, vecLen]
        rv_eval []
      c48 := by
        rw [m48, rd 40 (by decide)]
        simp only [Env.wordsLen, Env.bcp, vecLen]
        rv_eval []
      c56 := by rw [hfs _ (Or.inl rfl)]; exact hc.c56
      c64 := by rw [hfs _ (Or.inr rfl)]; exact hc.c64
      c128 := by
        rw [m128, rd 56 (by decide)]
        simp only [Env.posPtr, Env.bcp, vecPtr]
        rv_eval []
      c136 := by
        rw [m136, rd 64 (by decide)]
        simp only [Env.posLen, Env.bcp, vecLen]
        rv_eval []
      c144 := by rw [m144, hm₁]; exact hc.c272
      c152 := by rw [m152, hm₁]; exact hc.c264
      c160 := by rw [m160, k₁ .x18 (by decide)]; exact hc.x18
      c168 := by rw [m168, k₁ .x9 (by decide)]; exact hc.x9
      heapL := by
        have := hc.heap
        exact ⟨by simp only [heapNext, hnext₂]; exact this.lo,
          by simp only [heapNext, hnext₂]; exact this.hi⟩
      monoL := by simp only [heapNext, hnext₂]; exact hc.mono
      lowIn := by simp only [heapNext, hnext₂]; exact hc.lowIn
      highIn := by simp only [heapNext, hnext₂]; exact hc.highIn
      bkIn := by simp only [heapNext, hnext₂]; exact hc.bkIn
      lowBk := hc.lowBk
      highBk := hc.highBk
      lowVals := by
        have hl := hc.lowIn
        simp only [heapNext] at hl
        change eListAt u₂ low (2 ^ min (s.getReg .x13).toNat 14) = Model.eqKernelRust
          ((eListAt s (s.getReg .x12) (s.getReg .x13).toNat).take (min (s.getReg .x13).toNat 14))
        rw [eListAt_congr fun n hn j hj ↦ hfr _ (by addr_omega [hl, hn, hj, hsp, hhi]),
          hc.lowVals]
      highVals := by
        have hl := hc.highIn
        simp only [heapNext] at hl
        change eListAt u₂ high (2 ^ ((s.getReg .x13).toNat - min (s.getReg .x13).toNat 14)) =
          Model.eqKernelRust ((eListAt s (s.getReg .x12) (s.getReg .x13).toNat).drop
            (min (s.getReg .x13).toNat 14))
        rw [eListAt_congr fun n hn j hj ↦ hfr _ (by addr_omega [hl, hn, hj, hsp, hhi]),
          hc.highVals]
      bkVals := by
        have hl := hc.bkIn
        simp only [heapNext] at hl
        rw [eListAt_congr fun n hn j hj ↦ hfr _ (by addr_omega [hl, hn, hj, hsp, hhi]), hc.bkVals]
      frame := ((hc.frame.trans (Transcript.DFrame.of_same hm₁ fun _ ↦ False) fun _ h ↦ h.elim).trans
        (Transcript.DFrame.of_byteFrame bf₂)
        fun a ha ↦ Or.inl (by addr_omega [ha, hsp])).mono fun a h ↦ by
          simp only [Fresh, heapNext, hnext₂] at h ⊢; exact h }
  · exact {
      x13 := by rw [b80010f04_x13 h₂, e8₁, rd 8 (by decide)]; rfl
      x12 := b80010f04_x12 h₂
      x19 := b80010f04_x19 h₂
      x11 := b80010f04_x11 h₂
      x5 := b80010f04_x5 h₂
      x17 := b80010f04_x17 h₂
      x16 := b80010f04_x16 h₂
      x9 := by rw [k₂ .x9 (by decide), k₁ .x9 (by decide)]; exact hc.x9
      x18 := by rw [k₂ .x18 (by decide), k₁ .x18 (by decide)]; exact hc.x18
      x20 := by rw [b80010f04_x20 h₂, e2₁]; rv_eval []; rw [hm₁]; exact hc.c264
      x21 := by rw [b80010f04_x21 h₂, e2₁]; rv_eval []; rw [hm₁]; exact hc.c272
      x23 := by rw [b80010f04_x23 h₂, e2₁]; rv_eval []
      nonempty := h0 }

end Rv64Verifier.Proofs.Bytecode.Eval
