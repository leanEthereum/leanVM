import Rv64Verifier.Proofs.Bytecode.EvalBk

/-!
# `Bytecode::evaluate`: into a block's buckets

From the zeroed bit sums (`ZDone`, `0x80011394`): the block's `bytes_end`, checked, saved, and the
walk over its buckets set up (`BkInv`), or straight to `BkDone` when it has none.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

variable {e : Env}

set_option maxHeartbeats 4000000 in
theorem bk_start (he : EnvOk e) {t : MachineState} {i : Nat} (hz : ZDone e t i)
    (hpc : t.pc = 0x80011394) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x80011618 ∧ BkDone e u i) ∨
      (u.pc = 0x800113c8 ∧ BkInv e u i (e.st i).bytesStart)) := by
  have hsp := he.sp
  have hst := he.pre.stack.valid
  have hbk := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hbk hh
  have hbc := he.pre.bcClear.blocks
  have hbm := he.pre.bc.blocks
  have hba := he.pre.bc.blocksAlign
  have hlen := bc_blocks_length e
  have hi := hz.lt
  have e2 : t.getReg .x2 = e.s.getReg .x2 - 1968 := hz.sp
  have hblk := blk_eq e hi
  have hbe : (e.blk i).bytesEnd =
      (e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16)).toNat := by
    rw [hblk, bc_blocks e hi]
  have hwe : (e.blk i).wordsEnd = (e.bc.blocks[i]'hi).wordsEnd := by rw [hblk]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011394_spec hpc (by
    rv_eval [hz.x13]
    valid_in hbm [hbm, hba, hi, hlen])
  have k₁ := b80011394_keeps h₁
  have hbe' : t.getMem (t.getReg .x13 + 16) =
      e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16) := by
    rw [hz.x13]
    exact hz.mem.bc he hbc hbm (by addr_omega [hbm, hi, hlen]) (by addr_omega [hbm, hi, hlen])
  by_cases hc : (t.getMem (t.getReg .x13 + 16)).toNat < (t.getReg .x11).toNat
  · exact ⟨u₁, hr₁, Or.inl (dead_of_fetch (by rw [b80011394_pc_taken h₁ hc]; exact trap))⟩
  have hble : (e.st i).bytesStart ≤ (e.blk i).bytesEnd := by
    rw [hbe, ← hz.bs, ← hbe']; exact Nat.not_lt.mp hc
  have x12₁ : u₁.getReg .x12 = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16) :=
    (b80011394_x12 h₁).trans hbe'
  have e2₁ : u₁.getReg .x2 = e.s.getReg .x2 - 1968 := (k₁ .x2 (by decide)).trans e2
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8001139c_spec
    (b80011394_pc_not_taken h₁ (Nat.not_lt.mp hc)) (by rv_eval [e2₁]; valid_access hst [hsp])
  have k₂ := b8001139c_keeps h₂
  have hbl : u₁.getMem (u₁.getReg .x2 + 40) = e.bytesLen := by
    rw [e2₁]; rv_eval []
    rw [b80011394_mem_same h₁, hz.mem.slot he]; exact he.c40
  by_cases hc₂ : (u₁.getMem (u₁.getReg .x2 + 40)).toNat < (u₁.getReg .x12).toNat
  · exact ⟨u₂, hr₁.trans hr₂, Or.inl (dead_of_fetch (by rw [b8001139c_pc_taken h₂ hc₂]; exact trap))⟩
  have hbend : (e.blk i).bytesEnd ≤ e.bc.bytes.length := by
    rw [bc_bytes_length, hbe, ← x12₁, ← hbl]; exact Nat.not_lt.mp hc₂
  have e2₂ : u₂.getReg .x2 = e.s.getReg .x2 - 1968 := (k₂ .x2 (by decide)).trans e2₁
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800113a4_spec
    (b8001139c_pc_not_taken h₂ (Nat.not_lt.mp hc₂)) (by rv_eval [e2₂]; valid_access hst [hsp])
  have k₃ := b800113a4_keeps h₃
  have hf₃ := b800113a4_frame h₃ (by rw [e2₂]; addr_omega [hsp])
  rw [e2₂] at hf₃
  have m112 := b800113a4_m_x2_112 h₃
  rw [e2₂] at m112
  rv_eval [] at m112
  have hm₃ : ∀ a, ¬ Within a (e.s.getReg .x2 - 1968 + 112) 8 → u₃.getMem a = t.getMem a :=
    fun a ha ↦ by rw [hf₃ a ha, b8001139c_mem_same h₂, b80011394_mem_same h₁]
  have K₃ : ∀ r ∈ [Reg.x2, .x9, .x11, .x18, .x19, .x20, .x21, .x23], u₃.getReg r = t.getReg r :=
    fun r hr ↦ by rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have hmid : Mid e u₃ i := hz.toMid.of_mem he (fun a ha ↦ hm₃ a (by addr_omega [ha, hsp]))
    (fun a ha ↦ hm₃ a (by addr_omega [ha, hsp, hbk, hh])) K₃
  have hzero : eListAt u₃ (e.s.getReg .x2 - 1688) 64 = List.replicate 64 0 :=
    (eListAt_congr fun n hn j hj ↦ hm₃ _ (by addr_omega [hsp, hn, hj])).trans hz.zero
  have hnext : u₃.getMem (e.s.getReg .x2 - 1896) = e.blocksPtr + BitVec.ofNat 64 (24 * (i + 1)) :=
    (hm₃ _ (by addr_omega [hsp])).trans hz.next
  have hpe : (u₃.getReg .x19).toNat = e.pe i := by
    rw [hmid.x19, Env.pe, hwe]
  have hbks : eListAt u₃ e.bk 2048 = (e.bf i 0).1 := by
    rw [hmid.buckets, bf_zero, hwe]
  have hsum0 : eListAt u₃ (e.s.getReg .x2 - 1688) 64 = (e.bf i 0).2 := by rw [hzero, bf_zero]
  have x11₂ : u₂.getReg .x11 = t.getReg .x11 := by rw [k₂ .x11 (by decide), k₁ .x11 (by decide)]
  have x12₂ : u₂.getReg .x12 = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16) := by
    rw [k₂ .x12 (by decide), x12₁]
  by_cases hemp : u₂.getReg .x11 = u₂.getReg .x12
  · have hz0 : (e.blk i).bytesEnd - (e.st i).bytesStart = 0 := by
      rw [hbe, ← hz.bs, ← x11₂, hemp, x12₂]; simp
    refine ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inl ⟨b800113a4_pc_taken h₃ hemp, ?_⟩)⟩
    exact { hmid.toRegs with
      lt := hi
      ptr := hmid.ptr
      next := hnext
      we := hmid.we
      be := m112.trans x12₂
      total := hmid.total
      x19 := hpe
      blo := hble
      bend := hbend
      buckets := by rw [hz0]; exact hbks
      sums := by rw [hz0]; exact hsum0 }
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800113ac_spec (b800113a4_pc_not_taken h₃ hemp) (by
    rv_eval [(K₃ .x2 (by decide)).trans e2]; and_intros <;> valid_access hst [hsp])
  have k₄ := b800113ac_keeps h₄
  have hf₄ := b800113ac_frame h₄ (by rw [K₃ .x2 (by decide), e2]; addr_omega [hsp])
  rw [K₃ .x2 (by decide), e2] at hf₄
  have m176 := b800113ac_m_x2_176 h₄
  rw [K₃ .x2 (by decide), e2] at m176
  rv_eval [] at m176
  have hm₄ : ∀ a, ¬ Within a (e.s.getReg .x2 - 1968 + 176) 8 → u₄.getMem a = u₃.getMem a := hf₄
  have K₄ : ∀ r ∈ [Reg.x2, .x9, .x18, .x19, .x20, .x21, .x23], u₄.getReg r = u₃.getReg r :=
    fun r hr ↦ k₄ r (mem_of_mem hr _)
  have hregs : Regs e u₄ := {
    sp := (K₄ .x2 (by decide)).trans hmid.sp
    mem := hmid.mem.frame fun a ha ↦ hm₄ a (by addr_omega [ha, hsp])
    x9 := (K₄ .x9 (by decide)).trans hmid.x9
    x18 := by rw [K₄ .x18 (by decide)]; exact hmid.x18
    x20 := (K₄ .x20 (by decide)).trans hmid.x20
    x21 := (K₄ .x21 (by decide)).trans hmid.x21
    x23 := (K₄ .x23 (by decide)).trans hmid.x23 }
  have hbsl : (e.st i).bytesStart < (e.blk i).bytesEnd := by
    refine Nat.lt_of_le_of_ne hble fun h ↦ hemp ?_
    apply BitVec.eq_of_toNat_eq
    rw [x11₂, hz.bs, h, hbe, x12₂]
  have hbsp : u₃.getMem (u₃.getReg .x2 + 16) = e.bytesPtr := by
    rw [K₃ .x2 (by decide), e2]; rv_eval []
    rw [hmid.mem.slot he]; exact he.c16
  have hbmap := he.pre.bc.bytes
  have hbl' := bc_bytes_length e
  simp only [Mapped, Env.bytesLen, Env.bcp] at hbmap hbl'
  refine ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr ⟨b800113ac_pc h₄, ?_⟩)⟩
  exact { hregs with
    lt := hi
    ptr := (hm₄ _ (by addr_omega [hsp])).trans hmid.ptr
    next := (hm₄ _ (by addr_omega [hsp])).trans hnext
    we := (hm₄ _ (by addr_omega [hsp])).trans hmid.we
    be := (hm₄ _ (by addr_omega [hsp])).trans (m112.trans x12₂)
    total := by
      rw [hm₄ _ (by addr_omega [hsp]), hm₄ _ (by addr_omega [hsp]), hm₄ _ (by addr_omega [hsp])]
      exact hmid.total
    s3 := by rw [m176]; exact hpe
    x19 := by rw [K₄ .x19 (by decide)]; exact hpe
    blo := Nat.le_refl _
    bhi := hbsl
    bend := hbend
    x10 := by rw [b800113ac_x10 h₄, hbsp, mul2, K₃ .x11 (by decide), hz.bs]
    x11 := by
      rw [b800113ac_x11 h₄, K₃ .x2 (by decide), e2]
      rv_eval []
      have hb2 : ((e.blk i).bytesEnd : Nat) * 2 < 2 ^ 64 := by omega
      rw [m112, x12₂, K₃ .x11 (by decide), mul2, mul2, BitVec.toNat_sub_of_le]
      · simp only [BitVec.toNat_ofNat]
        rw [← hbe, hz.bs]
        omega
      · rw [BitVec.le_def]
        simp only [BitVec.toNat_ofNat]
        rw [← hbe, hz.bs]
        omega
    buckets := by
      rw [Nat.sub_self]
      exact (buckets_congr he fun a ha ↦ hm₄ a (by addr_omega [ha, hsp, hbk, hh])).trans hbks
    sums := by
      rw [Nat.sub_self]
      exact (eListAt_congr fun n hn j hj ↦ hm₄ _ (by addr_omega [hsp, hn, hj])).trans hsum0 }

end Rv64Verifier.Proofs.Bytecode.Eval
