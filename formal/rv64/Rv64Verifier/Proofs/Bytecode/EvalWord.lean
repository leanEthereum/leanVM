import Rv64Verifier.Proofs.Bytecode.EvalAdd
import Rv64Verifier.Proofs.Bytecode.EvalSteps
import Rv64Verifier.Proofs.Bytecode.EvalHead

/-!
# `Bytecode::evaluate`: one word of a block

`0x800110d0` reads the word's `positions_end`, trapping unless it is at least where its
positions start, `0x800110d8` unless it is at most `positions.len()`; `0x800110e0` reads the word
and skips the sum if it has no positions (`0x800110e8`); `0x800110f8` sets up the sum over them
(`SInv`), which `sum_body` advances a position at a time. `AInv`: the sum done, at `0x80011150`.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem limbs_zero_eq : limbs (0 : E) = (0, 0, 0) := by
  decide +kernel

theorem mul2 (x : Word) : x * 2 = BitVec.ofNat 64 (2 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [Sym.wordToNatLit]
  omega

namespace Env

/-- Word `j`'s entry: the word and where its positions end. -/
def wd (e : Env) (j : Nat) : BitVec 64 × Nat := e.bc.words.getD j (0, 0)

/-- Where the positions of word `j` of block `i` start. -/
def ps (e : Env) (i j : Nat) : Nat := (e.wf i (j - (e.st i).wordsStart)).2

end Env

/-- At word `j` of block `i`, its entry read and checked. -/
structure Word0 (e : Env) (t : MachineState) (i j : Nat) : Prop extends Blk e t i where
  jlo : (e.st i).wordsStart ≤ j
  jhi : j < (e.bc.blocks[i]'lt).wordsEnd
  x13 : t.getReg .x13 = e.wordsPtr + BitVec.ofNat 64 (16 * j)
  x12 : t.getReg .x12 = e.wordsPtr + BitVec.ofNat 64 (16 * (e.bc.blocks[i]'lt).wordsEnd)
  buckets : eListAt t e.bk 2048 = (e.wf i (j - (e.st i).wordsStart)).1
  pslo : e.ps i j ≤ (e.wd j).2
  pend : (e.wd j).2 ≤ e.bc.positions.length
  x19 : (t.getReg .x19).toNat = (e.wd j).2
  x17 : t.getReg .x17 = (e.wd j).1

/-- Word `j`'s positions summed (`0x80011150`). -/
structure AInv (e : Env) (t : MachineState) (i j : Nat) : Prop extends Word0 e t i j where
  acc : (t.getReg .x16, t.getReg .x15, t.getReg .x14) =
    limbs (memberSumRust e.lowW ((e.bc.positions.drop (e.ps i j)).take ((e.wd j).2 - e.ps i j)))

/-- Summing word `j`'s positions, before position `p` (`0x80011114`). -/
structure SInv (e : Env) (t : MachineState) (i j p : Nat) : Prop extends Word0 e t i j where
  plo : e.ps i j ≤ p
  phi : p < (e.wd j).2
  x5 : t.getReg .x5 = e.posPtr + BitVec.ofNat 64 (2 * p)
  x6 : (t.getReg .x6).toNat = (e.wd j).2 - p
  acc : (t.getReg .x16, t.getReg .x15, t.getReg .x14) =
    limbs (memberSumRust e.lowW ((e.bc.positions.drop (e.ps i j)).take (p - e.ps i j)))

variable {e : Env}

/-- `Blk` over a step that writes nothing and keeps the registers it names. -/
theorem Blk.of_same {t t' : MachineState} {i : Nat} (hb : Blk e t i)
    (hm : ∀ a, t'.getMem a = t.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x9, .x11, .x18, .x20, .x21, .x23], t'.getReg r = t.getReg r) :
    Blk e t' i where
  sp := (hr .x2 (by decide)).trans hb.sp
  mem := hb.mem.same hm
  x9 := (hr .x9 (by decide)).trans hb.x9
  x18 := by rw [hr .x18 (by decide)]; exact hb.x18
  x20 := (hr .x20 (by decide)).trans hb.x20
  x21 := (hr .x21 (by decide)).trans hb.x21
  x23 := (hr .x23 (by decide)).trans hb.x23
  lt := hb.lt
  ptr := by rw [hm]; exact hb.ptr
  we := by rw [hm]; exact hb.we
  total := by rw [hm, hm, hm]; exact hb.total
  bs := by rw [hr .x11 (by decide)]; exact hb.bs
  wsle := hb.wsle
  wele := hb.wele

theorem wd_eq (e : Env) {j : Nat} (hj : j < e.bc.words.length) :
    e.wd j = (e.s.getMem (e.wordsPtr + BitVec.ofNat 64 (16 * j)),
      (e.s.getMem (e.wordsPtr + BitVec.ofNat 64 (16 * j) + 8)).toNat) := by
  rw [Env.wd, List.getD_eq_getElem _ _ hj, bc_words e hj]

set_option maxHeartbeats 2000000 in
/-- Word `j`'s entry, then the sum's start. -/
theorem word_start (he : EnvOk e) {t : MachineState} {i j : Nat} (hw : WInv e t i j)
    (hpc : t.pc = 0x800110d0) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x80011150 ∧ AInv e u i j) ∨
      (u.pc = 0x80011114 ∧ SInv e u i j (e.ps i j))) := by
  have hsp := he.sp
  have hst := he.pre.stack.valid
  have hwc := he.pre.bcClear.words
  have hwm := he.pre.bc.words
  have hwa := he.pre.bc.wordsAlign
  have hlen := bc_words_length e
  have hj : j < e.bc.words.length := Nat.lt_of_lt_of_le hw.jhi hw.wele
  have hx13 := hw.x13
  have e2 := hw.sp
  simp only [fp] at e2
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800110d0_spec hpc (by
    rv_eval [hx13]
    valid_in hwm [hwm, hwa, hj, hlen])
  have k₁ := b800110d0_keeps h₁
  have hpe : t.getMem (t.getReg .x13 + 8) = e.s.getMem (e.wordsPtr + BitVec.ofNat 64 (16 * j) + 8) := by
    rw [hx13]
    exact hw.mem.bc he hwc hwm (by addr_omega [hwm, hj, hlen]) (by addr_omega [hwm, hj, hlen])
  have hwd := wd_eq e hj
  have x19₁ : (t₁.getReg .x19).toNat = (e.wd j).2 := by rw [b800110d0_x19 h₁, hpe, hwd]
  by_cases hc : (t.getMem (t.getReg .x13 + 8)).toNat < (t.getReg .x6).toNat
  · exact ⟨t₁, hr₁, Or.inl (dead_of_fetch (by rw [b800110d0_pc_taken h₁ hc]; exact trap))⟩
  have hpslo : e.ps i j ≤ (e.wd j).2 := by
    rw [Env.ps, ← hw.x6, hwd]; rw [hpe] at hc; exact Nat.not_lt.mp hc
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800110d8_spec
    (b800110d0_pc_not_taken h₁ (Nat.not_lt.mp hc)) (by
      rv_eval [k₁ .x2 (by decide), e2]; valid_access hst [hsp])
  have k₂ := b800110d8_keeps h₂
  have hpl : t₁.getMem (t₁.getReg .x2 + 136) = e.posLen := by
    rw [k₁ .x2 (by decide), e2]; rv_eval []
    rw [b800110d0_mem_same h₁, hw.mem.slot he]; exact he.c136
  by_cases hc₂ : (t₁.getMem (t₁.getReg .x2 + 136)).toNat < (t₁.getReg .x19).toNat
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl (dead_of_fetch (by rw [b800110d8_pc_taken h₂ hc₂]; exact trap))⟩
  have hpend : (e.wd j).2 ≤ e.bc.positions.length := by
    rw [bc_positions_length, ← x19₁, ← hpl]; exact Nat.not_lt.mp hc₂
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800110e0_spec
    (b800110d8_pc_not_taken h₂ (Nat.not_lt.mp hc₂)) (by
      rv_eval [k₂ .x13 (by decide), k₁ .x13 (by decide), hx13]
      valid_in hwm [hwm, hwa, hj, hlen])
  have k₃ := b800110e0_keeps h₃
  have hm₃ : ∀ a, t₃.getMem a = t.getMem a := fun a ↦ by
    rw [b800110e0_mem_same h₃, b800110d8_mem_same h₂, b800110d0_mem_same h₁]
  have x17₃ : t₃.getReg .x17 = (e.wd j).1 := by
    rw [b800110e0_x17 h₃, k₂ .x13 (by decide), k₁ .x13 (by decide), hx13, b800110d8_mem_same h₂,
      b800110d0_mem_same h₁, hw.mem.bc he hwc hwm (by addr_omega [hwm, hj, hlen])
        (by addr_omega [hwm, hj, hlen]), hwd]
  have kk : ∀ r ∈ [Reg.x2, .x6, .x9, .x11, .x12, .x13, .x18, .x20, .x21, .x23],
      t₃.getReg r = t.getReg r := fun r hr ↦ by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x19₃ : t₃.getReg .x19 = t₁.getReg .x19 := by rw [k₃ .x19 (by decide), k₂ .x19 (by decide)]
  have hb₃ : Blk e t₃ i := hw.toBlk.of_same hm₃ fun r hr ↦ kk r (mem_of_mem hr _)
  have w0 : Word0 e t₃ i j := { hb₃ with
    jlo := hw.jlo
    jhi := hw.jhi
    x13 := (kk .x13 (by decide)).trans hx13
    x12 := (kk .x12 (by decide)).trans hw.x12
    buckets := (buckets_congr he fun a _ ↦ hm₃ a).trans hw.buckets
    pslo := hpslo
    pend := hpend
    x19 := by rw [x19₃]; exact x19₁
    x17 := x17₃ }
  have x6₃ : (t₃.getReg .x6).toNat = e.ps i j := by rw [kk .x6 (by decide)]; exact hw.x6
  by_cases hz : t₂.getReg .x19 = t₂.getReg .x6
  · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800110e8_spec (b800110e0_pc_not_taken h₃ hz) trivial
    have k₄ := b800110e8_keeps h₄
    have hpe' : (e.wd j).2 = e.ps i j := by
      rw [← x19₁, ← x6₃, kk .x6 (by decide), ← k₂ .x19 (by decide), hz, k₂ .x6 (by decide),
        k₁ .x6 (by decide)]
    refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inl ⟨b800110e8_pc h₄, ?_⟩)⟩
    exact { w0.toBlk.of_same (b800110e8_mem_same h₄) (fun r hr ↦ k₄ r (mem_of_mem hr _)) with
      jlo := w0.jlo
      jhi := w0.jhi
      x13 := (k₄ .x13 (by decide)).trans w0.x13
      x12 := (k₄ .x12 (by decide)).trans w0.x12
      buckets := (buckets_congr he fun a _ ↦ b800110e8_mem_same h₄ a).trans w0.buckets
      pslo := hpslo
      pend := hpend
      x19 := by rw [k₄ .x19 (by decide)]; exact w0.x19
      x17 := (k₄ .x17 (by decide)).trans x17₃
      acc := by
        rw [b800110e8_x16 h₄, b800110e8_x15 h₄, b800110e8_x14 h₄, hpe', Nat.sub_self,
          List.take_zero]
        exact limbs_zero_eq.symm }
  · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800110f8_spec (b800110e0_pc_taken h₃ hz) (by
      rv_eval [kk .x2 (by decide), e2]; valid_access hst [hsp])
    have k₄ := b800110f8_keeps h₄
    have hpp : t₃.getMem (t₃.getReg .x2 + 128) = e.posPtr := by
      rw [kk .x2 (by decide), e2]; rv_eval []
      rw [hm₃, hw.mem.slot he]; exact he.c128
    have hlt : e.ps i j < (e.wd j).2 := by
      refine Nat.lt_of_le_of_ne hpslo fun h ↦ hz ?_
      apply BitVec.eq_of_toNat_eq
      rw [k₂ .x19 (by decide), x19₁, k₂ .x6 (by decide), k₁ .x6 (by decide), hw.x6]
      exact h.symm
    refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr ⟨b800110f8_pc h₄, ?_⟩)⟩
    exact { w0.toBlk.of_same (b800110f8_mem_same h₄) (fun r hr ↦ k₄ r (mem_of_mem hr _)) with
      jlo := w0.jlo
      jhi := w0.jhi
      x13 := (k₄ .x13 (by decide)).trans w0.x13
      x12 := (k₄ .x12 (by decide)).trans w0.x12
      buckets := (buckets_congr he fun a _ ↦ b800110f8_mem_same h₄ a).trans w0.buckets
      pslo := hpslo
      pend := hpend
      x19 := by rw [k₄ .x19 (by decide)]; exact w0.x19
      x17 := (k₄ .x17 (by decide)).trans x17₃
      plo := Nat.le_refl _
      phi := hlt
      x5 := by rw [b800110f8_x5 h₄, hpp, mul2, x6₃]
      x6 := by
        rw [b800110f8_x6 h₄, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
          rw [x6₃, x19₃, x19₁]; exact hpslo)), x19₃, x19₁, x6₃]
      acc := by
        rw [b800110f8_x16 h₄, b800110f8_x15 h₄, b800110f8_x14 h₄, Nat.sub_self, List.take_zero]
        exact limbs_zero_eq.symm }

end Rv64Verifier.Proofs.Bytecode.Eval
