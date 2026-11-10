import Rv64Verifier.Proofs.Bytecode.EvalBkLoop
import Rv64Verifier.Proofs.Bytecode.EvalTail

/-!
# `Bytecode::evaluate`: one block, and all of them

`block_step`: from the loop's head before block `i` (`Outer`), its words (`head`, `words_loop`),
its bit sums zeroed (`zero_loop`), its buckets (`bk_start`, `bk_loop`) and its end (`tail`), to the
head before block `i + 1`, the state being `blockStepRust`'s (`st_succ`), or, after the last
block, to `Ok`. `blocks_loop` runs them all.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84

variable {e : Env}

/-- `evaluateRust`'s state after block `i`. -/
theorem st_succ (e : Env) {i : Nat} (hi : i < e.bc.blocks.length) :
    e.st (i + 1) = ⟨(e.bf i ((e.blk i).bytesEnd - (e.st i).bytesStart)).1, (e.blk i).wordsEnd,
      e.pe i, (e.blk i).bytesEnd,
      e.total' i (e.bf i ((e.blk i).bytesEnd - (e.st i).bytesStart)).2⟩ := by
  rw [Env.st, evalAfter_succ _ _ _ hi, ← blk_eq e hi]
  simp only [blockStepRust, Env.bf, Env.pe, Env.wf, Env.total', Env.st]
  rw [List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some, ← blk_eq e hi]

/-- The words' and the buckets' phases of block `i`: to `BkDone`. -/
theorem block_body (he : EnvOk e) {t : MachineState} {i : Nat} (ho : Outer e t i)
    (hpc : t.pc = 0x80011090) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x80011618 ∧ BkDone e u i)) := by
  obtain ⟨u₁, hr₁, hm⟩ : ∃ u, Reaches Image.code t u ∧
      (Dead Image.code u ∨ (u.pc = 0x8001136c ∧ Mid e u i)) := by
    obtain ⟨u, hr, hd | hm | ⟨hu, hw⟩⟩ := head he ho hpc
    · exact ⟨u, hr, Or.inl hd⟩
    · exact ⟨u, hr, Or.inr hm⟩
    · obtain ⟨v, hv, hx⟩ := words_loop he hw hu
      exact ⟨v, hr.trans hv, hx⟩
  rcases hm with hd | ⟨hu₁, hm⟩
  · exact ⟨u₁, hr₁, Or.inl hd⟩
  obtain ⟨u₂, hr₂, hu₂, hz⟩ := zero_loop he hm hu₁
  obtain ⟨u₃, hr₃, hd | hdone | ⟨hu₃, hb⟩⟩ := bk_start he hz hu₂
  · exact ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  · exact ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inr hdone⟩
  · obtain ⟨u₄, hr₄, hx⟩ := bk_loop he hb hu₃
    exact ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), hx⟩

/-- **Block `i`**: to the head before block `i + 1`, or to `Ok(total)` after the last. -/
theorem block_step (hMul : MulSpec) (he : EnvOk e) {t : MachineState} {i : Nat}
    (ho : Outer e t i) (hpc : t.pc = 0x80011090) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x80011090 ∧ Outer e u (i + 1)) ∨
      (u.pc = 0x800116f8 ∧ Regs e u ∧ i + 1 = e.bc.blocks.length ∧
        (u.getReg .x5, u.getReg .x17, u.getReg .x16) = limbs (e.st (i + 1)).total)) := by
  obtain ⟨u, hr, hd | ⟨hu, hb⟩⟩ := block_body he ho hpc
  · exact ⟨u, hr, Or.inl hd⟩
  have hi := hb.lt
  have ht : Tail e u i (e.bf i ((e.blk i).bytesEnd - (e.st i).bytesStart)).2
      (e.bf i ((e.blk i).bytesEnd - (e.st i).bytesStart)).1 (e.pe i) :=
    { hb.toRegs with
      lt := hi
      x19 := hb.x19
      ptr := hb.ptr
      next := hb.next
      we := hb.we
      be := hb.be
      total := hb.total
      sums := hb.sums
      buckets := hb.buckets }
  have hst := st_succ e hi
  have hblk := bc_blocks e hi
  rw [← blk_eq e hi] at hblk
  obtain ⟨v, hv, hd | ⟨hvp, hreg, hlt, x13, x12, x11, x19, htot, hbk⟩ | ⟨hvp, hreg, heq, htot⟩⟩ :=
    tail hMul he ht hu
  · exact ⟨v, hr.trans hv, Or.inl hd⟩
  · refine ⟨v, hr.trans hv, Or.inr (Or.inl ⟨hvp, { hreg with
      lt := hlt
      x13 := x13
      ws := by rw [hst, x12, hblk]
      ps := by rw [hst, x19]
      bs := by rw [hst, x11, hblk]
      total := by rw [hst, htot]
      buckets := by rw [hst, hbk] }⟩)⟩
  · exact ⟨v, hr.trans hv, Or.inr (Or.inr ⟨hvp, hreg, heq, by rw [hst, htot]⟩)⟩

/-- **Every block**: from the head before block `i`, to `Ok` with the total after the last. -/
theorem blocks_loop (hMul : MulSpec) (he : EnvOk e) {t : MachineState} {i : Nat}
    (ho : Outer e t i) (hpc : t.pc = 0x80011090) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x800116f8 ∧ Regs e u ∧
      (u.getReg .x5, u.getReg .x17, u.getReg .x16) = limbs (e.st e.bc.blocks.length).total)) := by
  refine Reaches.loop (fun t ↦ ∃ i, t.pc = 0x80011090 ∧ Outer e t i)
    (fun t ↦ e.bc.blocks.length - ((t.getReg .x13).toNat - e.blocksPtr.toNat) / 24) _
    (fun t ⟨i, hpc, ho⟩ ↦ ?_) t ⟨i, hpc, ho⟩
  obtain ⟨u, hr, hd | ⟨hu, ho'⟩ | ⟨hu, hreg, heq, htot⟩⟩ := block_step hMul he ho hpc
  · exact Or.inl ⟨u, hr, Or.inl hd⟩
  · refine Or.inr ⟨u, hr, ⟨i + 1, hu, ho'⟩, ?_⟩
    have hbm := he.pre.bc.blocks
    have hlen := bc_blocks_length e
    have h1 := ho'.lt
    simp only [Mapped, Env.blocksLen, Env.blocksPtr, Env.bcp] at hbm hlen ⊢
    rw [ho'.x13, ho.x13]
    simp only [Env.blocksPtr, Env.bcp]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · exact Or.inl ⟨u, hr, Or.inr ⟨hu, hreg, by rw [← heq]; exact htot⟩⟩

end Rv64Verifier.Proofs.Bytecode.Eval
