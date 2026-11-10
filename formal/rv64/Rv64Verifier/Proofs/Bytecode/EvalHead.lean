import Rv64Verifier.Proofs.Bytecode.EvalLoop

/-!
# `Bytecode::evaluate`: a block's start

`0x80011090` reads `block.words_end` and saves the block's pointer, trapping unless
`words_start <= words_end`; `0x8001109c` traps unless `words_end <= words.len()`; `0x800110a4`
saves `words_end` and the total, and skips the words if there are none (`Mid`); `0x800110b8` sets
up the walk over them (`WInv`).
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem trap : Image.code.fetch 0x80011748 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem mul16 (x : Word) : x * 16 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [Sym.wordToNatLit]
  omega

theorem wf_zero (e : Env) (i : Nat) : e.wf i 0 = ((e.st i).buckets, (e.st i).positionsStart) := by
  simp [Env.wf]

variable {e : Env}

set_option maxHeartbeats 2000000 in
theorem head (he : EnvOk e) {t : MachineState} {i : Nat} (ho : Outer e t i)
    (hpc : t.pc = 0x80011090) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨
      (u.pc = 0x8001136c ∧ Mid e u i) ∨ (u.pc = 0x800110d0 ∧ WInv e u i (e.st i).wordsStart)) := by
  have hsp := he.sp
  have hst := he.pre.stack.valid
  have hbc := he.pre.bcClear.blocks
  have hbm := he.blocksMem ho.lt
  have hba := he.pre.bc.blocksAlign
  have hlen := bc_blocks_length e
  have hi := ho.lt
  have hbk := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hbk hh
  have e2 : t.getReg .x2 = e.s.getReg .x2 - 1968 := ho.sp
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011090_spec hpc (by
    rv_eval [e2, ho.x13]
    and_intros <;> first
      | valid_access hst [hsp]
      | valid_in hbm [hbm, hba, hi, hlen]
      | addr_omega [hbc, hbm, hi, hlen, hsp])
  have k₁ := b80011090_keeps h₁
  have x13₁ := b80011090_x13 h₁
  have hwe : t.getMem (t.getReg .x13 + 8) = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8) := by
    rw [ho.x13]
    exact ho.mem.bc he hbc hbm (by addr_omega [hbm, hi, hlen]) (by addr_omega [hbm, hi, hlen])
  have hblk := bc_blocks e hi
  have hwe' : (e.bc.blocks[i]'hi).wordsEnd = (e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8)).toNat := by
    rw [hblk]
  by_cases hc : (t.getMem (t.getReg .x13 + 8)).toNat < (t.getReg .x12).toNat
  · exact ⟨t₁, hr₁, Or.inl (dead_of_fetch (by rw [b80011090_pc_taken h₁ hc]; exact trap))⟩
  have hm₁ : LoopMem e t₁ := ho.mem.step h₁ (by rv_eval [e2]; addr_omega [hsp])
  have e2₁ : t₁.getReg .x2 = e.s.getReg .x2 - 1968 := (k₁ .x2 (by decide)).trans e2
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8001109c_spec
    (b80011090_pc_not_taken h₁ (Nat.not_lt.mp hc)) (by rv_eval [e2₁]; valid_access hst [hsp])
  have k₂ := b8001109c_keeps h₂
  have hwl : t₁.getMem (t₁.getReg .x2 + 48) = e.wordsLen := by
    rw [e2₁]; rv_eval []
    rw [hm₁.slot he]; exact he.c48
  have x13₁' : t₁.getReg .x13 = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8) :=
    x13₁.trans hwe
  by_cases hc₂ : (t₁.getMem (t₁.getReg .x2 + 48)).toNat < (t₁.getReg .x13).toNat
  · exact ⟨t₂, hr₁.trans hr₂,
      Or.inl (dead_of_fetch (by rw [b8001109c_pc_taken h₂ hc₂]; exact trap))⟩
  have hm₂ : LoopMem e t₂ := hm₁.same (b8001109c_mem_same h₂)
  have e2₂ : t₂.getReg .x2 = e.s.getReg .x2 - 1968 := (k₂ .x2 (by decide)).trans e2₁
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800110a4_spec
    (b8001109c_pc_not_taken h₂ (Nat.not_lt.mp hc₂)) (by
      rv_eval [e2₂]; and_intros <;> valid_access hst [hsp])
  have k₃ := b800110a4_keeps h₃
  have hm₃ : LoopMem e t₃ := hm₂.step h₃ (by rv_eval [e2₂]; and_intros <;> addr_omega [hsp])
  have e2₃ : t₃.getReg .x2 = e.s.getReg .x2 - 1968 := (k₃ .x2 (by decide)).trans e2₂
  have kt : ∀ r ∈ [Reg.x5, .x9, .x11, .x12, .x16, .x17, .x18, .x19, .x20, .x21, .x23],
      t₃.getReg r = t.getReg r := fun r hr ↦ by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x13₃ : t₃.getReg .x13 = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8) := by
    rw [k₃ .x13 (by decide), k₂ .x13 (by decide), x13₁']
  have hwle : (e.st i).wordsStart ≤ (e.bc.blocks[i]'hi).wordsEnd := by
    rw [hwe', ← ho.ws, ← hwe]; exact Nat.not_lt.mp hc
  have hwl' : (e.bc.blocks[i]'hi).wordsEnd ≤ e.bc.words.length := by
    rw [hwe', bc_words_length, ← x13₁', ← hwl]; exact Nat.not_lt.mp hc₂
  have m80 := b800110a4_m_x2_80 h₃
  have m88 := b800110a4_m_x2_88 h₃
  have m96 := b800110a4_m_x2_96 h₃
  have m104 := b800110a4_m_x2_104 h₃
  rw [e2₂] at m80 m88 m96 m104
  rv_eval [] at m80 m88 m96 m104
  have m120 := b80011090_m_x2_120 h₁
  rw [e2, ho.x13] at m120
  rv_eval [] at m120
  have hblk : Blk e t₃ i := {
    sp := e2₃
    mem := hm₃
    x9 := (kt .x9 (by decide)).trans ho.x9
    x18 := by rw [kt .x18 (by decide)]; exact ho.x18
    x20 := (kt .x20 (by decide)).trans ho.x20
    x21 := (kt .x21 (by decide)).trans ho.x21
    x23 := (kt .x23 (by decide)).trans ho.x23
    lt := hi
    ptr := by
      rw [h₃.frame _ (by rv_eval [e2₂]; and_intros <;> addr_omega [hsp]), b8001109c_mem_same h₂,
        m120]
    we := by rw [m80, k₂ .x13 (by decide), x13₁']
    total := by
      rw [m88, m96, m104, k₂ .x5 (by decide), k₂ .x17 (by decide), k₂ .x16 (by decide),
        k₁ .x5 (by decide), k₁ .x17 (by decide), k₁ .x16 (by decide)]
      exact ho.total
    bs := by rw [kt .x11 (by decide)]; exact ho.bs
    wsle := hwle
    wele := hwl' }
  have x12₃ : t₂.getReg .x12 = t.getReg .x12 := by rw [k₂ .x12 (by decide), k₁ .x12 (by decide)]
  by_cases hemp : t₂.getReg .x12 = t₂.getReg .x13
  · have hz : (e.bc.blocks[i]'hi).wordsEnd - (e.st i).wordsStart = 0 := by
      rw [hwe', ← ho.ws, ← x12₃, hemp, k₂ .x13 (by decide), x13₁']; simp
    refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inl ⟨b800110a4_pc_taken h₃ hemp, ?_⟩)⟩
    exact { hblk with
      x19 := by rw [hz, wf_zero, kt .x19 (by decide)]; exact ho.ps
      buckets := by
        rw [hz, wf_zero]
        exact (buckets_congr he fun a ha ↦ by
          rw [h₃.frame _ (by
            rv_eval [e2₂]; and_intros <;> addr_omega [ha, hsp, hbk, hh]), b8001109c_mem_same h₂,
            h₁.frame _ (by rv_eval [e2]; addr_omega [ha, hsp, hbk, hh])]).trans ho.buckets }
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800110b8_spec (b800110a4_pc_not_taken h₃ hemp)
    (by rv_eval [e2₃]; valid_access hst [hsp])
  have k₄ := b800110b8_keeps h₄
  have hm₄ := b800110b8_mem_same h₄
  have hwp : t₃.getMem (t₃.getReg .x2 + 24) = e.wordsPtr := by
    rw [e2₃]; rv_eval []; rw [hm₃.slot he]; exact he.c24
  have hne : (e.st i).wordsStart ≠ (e.bc.blocks[i]'hi).wordsEnd := by
    intro h
    apply hemp
    apply BitVec.eq_of_toNat_eq
    rw [x12₃, ho.ws, h, hwe', k₂ .x13 (by decide), x13₁']
  refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr ⟨b800110b8_pc h₄, ?_⟩)⟩
  exact {
    sp := (k₄ .x2 (by decide)).trans e2₃
    mem := hblk.mem.same hm₄
    x9 := (k₄ .x9 (by decide)).trans hblk.x9
    x18 := by rw [k₄ .x18 (by decide)]; exact hblk.x18
    x20 := (k₄ .x20 (by decide)).trans hblk.x20
    x21 := (k₄ .x21 (by decide)).trans hblk.x21
    x23 := (k₄ .x23 (by decide)).trans hblk.x23
    lt := hi
    ptr := by rw [hm₄]; exact hblk.ptr
    we := by rw [hm₄]; exact hblk.we
    total := by rw [hm₄, hm₄, hm₄]; exact hblk.total
    bs := by rw [k₄ .x11 (by decide)]; exact hblk.bs
    wsle := hwle
    wele := hwl'
    jlo := Nat.le_refl _
    jhi := Nat.lt_of_le_of_ne hwle hne
    x13 := by rw [b800110b8_x13 h₄, hwp, mul16, kt .x12 (by decide), ho.ws]
    x12 := by rw [b800110b8_x12 h₄, hwp, mul16, x13₃, ← hwe']
    x6 := by rw [b800110b8_x6 h₄, kt .x19 (by decide), Nat.sub_self, wf_zero]; exact ho.ps
    buckets := by
      rw [Nat.sub_self, wf_zero]
      exact (buckets_congr he fun a ha ↦ by
          rw [hm₄, h₃.frame _ (by
            rv_eval [e2₂]; and_intros <;> addr_omega [ha, hsp, hbk, hh]), b8001109c_mem_same h₂,
            h₁.frame _ (by rv_eval [e2]; addr_omega [ha, hsp, hbk, hh])]).trans ho.buckets }

end Rv64Verifier.Proofs.Bytecode.Eval
