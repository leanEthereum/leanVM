import Rv64Verifier.Proofs.Bytecode.EvalBkStart

/-!
# `Bytecode::evaluate`: the walk over a block's buckets

`bk_body` is one bucket (`bucketStepRust`): loaded, its sum taken and zeroed, credited to the
bit sums; `bk_loop` all of them, to `BkDone`.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

variable {e : Env}

theorem fetch_113c8 : Image.code.fetch 0x800113c8 = some (.base (.LHU .x16 .x10 0)) :=
  fetch_of (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem bk_body (he : EnvOk e) {t : MachineState} {i b : Nat} (hb : BkInv e t i b)
    (hpc : t.pc = 0x800113c8) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨
      (u.pc = 0x800113c8 ∧ BkInv e u i (b + 1)) ∨ (u.pc = 0x80011618 ∧ BkDone e u i)) := by
  have hsp := he.sp
  have hst := he.pre.stack.valid
  have hbk := he.bkIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hbk hh hlo
  have hbkm : Mapped e.bk 49152 := by simp only [Mapped]; omega
  have hbc := he.pre.bcClear.bytes
  have hbm := he.bytesMem (Nat.lt_of_lt_of_le hb.bhi hb.bend)
  have hba := he.pre.bc.bytesAlign
  have hblen := bc_bytes_length e
  have hbl : b < e.bc.bytes.length := Nat.lt_of_lt_of_le hb.bhi hb.bend
  have hb2 : 2 * b + 2 ≤ 2 * e.bytesLen.toNat := by rw [← hblen]; omega
  simp only [Env.bytesLen, Env.bcp] at hb2
  have hx10 := hb.x10
  simp only [Env.bytesPtr, Env.bcp] at hx10
  obtain ⟨u, hr, hx16, hreg, hm, hupc⟩ := lhu_bgeu hpc fetch_113c8 rfl br113cc (by decide)
    (by decide) (by rw [hx10]; refine valid_half hbm ?_ ?_ ?_ <;> addr_omega [hbm, hba, hb2])
  have hbyte : t.getHalfword (t.getReg .x10) = e.bc.bytes[b] := by
    rw [bc_bytes e hbl, hx10]
    exact hb.mem.bcHalf he hbc hbm (by addr_omega [hbm, hb2]) (by addr_omega [hbm, hb2])
      (by addr_omega [hbm, hba, hb2])
  rw [hbyte] at hx16 hupc
  generalize hcdef : e.bc.bytes[b] = c at hx16 hupc
  have hzx : ((c.zeroExtend 64 : Word)).toNat = c.toNat := by
    rw [BitVec.toNat_setWidth]; have := c.isLt; omega
  rw [hzx, hb.x21] at hupc
  simp only [Sym.wordToNatLit] at hupc
  by_cases hc : 2048 ≤ c.toNat
  · simp only [hc, ↓reduceIte] at hupc
    exact ⟨u, hr, Or.inl (dead_of_fetch (by rw [hupc]; exact trap))⟩
  simp only [hc, ↓reduceIte] at hupc
  have hc' : c.toNat < 2048 := by omega
  have hu2 : u.getReg .x2 = e.s.getReg .x2 - 1968 := (hreg .x2 (by decide)).trans hb.sp
  have hu20 : u.getReg .x20 = e.bk := (hreg .x20 (by decide)).trans hb.x20
  have hum : LoopMem e u := hb.mem.same hm
  -- `0x800113d0`: take the bucket's sum, zero it
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800113d0_spec hupc (by
    rv_eval [hu2, hu20, hx16, mul24, hzx]
    and_intros <;> first
      | valid_access hst [hsp]
      | valid_in hbkm [hbkm, hbk, hc']
      | addr_omega [hsp, hbk, hh, hc'])
  have k₂ := b800113d0_keeps h₂
  have s13 := b800113d0_x13 h₂
  have s14 := b800113d0_x14 h₂
  have s15 := b800113d0_x15 h₂
  have z1 := b800113d0_m1 h₂
  have z2 := b800113d0_m2 h₂
  have z3 := b800113d0_m3 h₂
  rw [hu20, hx16, mul24, hzx] at s13 s14 s15 z1 z2 z3
  have hbkfr : ∀ a, Within a e.bk 49152 →
      ¬ Within a (e.bk + BitVec.ofNat 64 (24 * c.toNat)) 24 → u₂.getMem a = u.getMem a :=
    fun a h1 h2 ↦ h₂.frame a (by
      rv_eval [hu2, hu20, hx16, mul24, hzx]; and_intros <;> addr_omega [h1, h2, hsp, hbk, hh, hc'])
  have hfr₂ : ∀ a, ¬ Within a e.bk 49152 → ¬ Within a (e.s.getReg .x2 - 1776) 16 →
      u₂.getMem a = u.getMem a := fun a h1 h2 ↦ h₂.frame a (by
      rv_eval [hu2, hu20, hx16, mul24, hzx]; and_intros <;> addr_omega [h1, h2, hsp, hbk, hh, hc'])
  have hBlen : c.toNat < (eListAt u e.bk 2048).length := by rw [eListAt_length]; exact hc'
  have hsum : (u₂.getReg .x13, u₂.getReg .x14, u₂.getReg .x15) =
      limbs ((eListAt u e.bk 2048).getD c.toNat 0) := by
    rw [List.getD_eq_getElem _ _ hBlen, eListAt_getElem, limbs_eAt, s13, s14, s15]
  have hbuck₂ : eListAt u₂ e.bk 2048 = (eListAt u e.bk 2048).set c.toNat 0 :=
    eListAt_set' hc' (by omega) (by
      apply eAt_eq_of_limbs
      rw [z3, z2, z1]
      decide +kernel) hbkfr
  have hpc₂ := b800113d0_pc_not_taken h₂ (by
    rw [hx16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, hzx, Nat.shiftRight_eq_div_pow]
    simp only [Sym.wordToNatLit]
    omega)
  have e2₂ : u₂.getReg .x2 = e.s.getReg .x2 - 1968 := (k₂ .x2 (by decide)).trans hu2
  have h16₂ : u₂.getReg .x16 = c.setWidth 64 := by rw [k₂ .x16 (by decide), hx16]
  -- `0x80011408`: credit it
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011408_spec hpc₂ (credit_obl he e2₂ h16₂ hc')
  obtain ⟨hsums, hfr₃⟩ := credit he h₃ e2₂ h16₂ hc' hsum
  have k₃ := b80011408_keeps h₃
  -- the frame from `t` to `u₃`: the bucket, two slots, the bit sums and one spill slot
  have hfr : ∀ a, ¬ Within a e.bk 49152 → ¬ Within a (e.s.getReg .x2 - 1792) 1640 →
      u₃.getMem a = t.getMem a := fun a h1 h2 ↦ by
    rw [hfr₃ a (by addr_omega [h2, hsp]) (by addr_omega [h2, hsp]),
      hfr₂ a h1 (by addr_omega [h2, hsp]), hm]
  have hslot (c' : Word) (hk : (8 ≤ c'.toNat ∧ c'.toNat ≤ 104) ∨ (1800 ≤ c'.toNat ∧ c'.toNat ≤ 1840) ∨
      (1904 ≤ c'.toNat ∧ c'.toNat ≤ 1960) := by decide) :
      u₃.getMem (e.s.getReg .x2 - c') = e.tL.getMem (e.s.getReg .x2 - c') := by
    rw [hfr _ (by addr_omega [hsp, hbk, hh, hk]) (by addr_omega [hsp, hk])]
    exact hb.mem.slot he hk
  have hm₃ : LoopMem e u₃ := hb.mem.frame fun a ha ↦ hfr a (by addr_omega [ha, hsp])
    (by addr_omega [ha, hsp])
  have hold (c' : Word) (hk : 1840 < c'.toNat ∧ c'.toNat ≤ 1904) :
      u₃.getMem (e.s.getReg .x2 - c') = t.getMem (e.s.getReg .x2 - c') :=
    hfr _ (by addr_omega [hsp, hbk, hh, hk]) (by addr_omega [hsp, hk])
  have hslot₂ (c' : Word) (hk : (1800 ≤ c'.toNat ∧ c'.toNat ≤ 1840)) :
      u₂.getMem (e.s.getReg .x2 - c') = e.tL.getMem (e.s.getReg .x2 - c') := by
    rw [hfr₂ _ (by addr_omega [hsp, hbk, hh, hk]) (by addr_omega [hsp, hk]), hm]
    exact hb.mem.slot he (Or.inr (Or.inl hk))
  have hold₂ (c' : Word) (hk : 1784 < c'.toNat ∧ c'.toNat ≤ 1904) :
      u₂.getMem (e.s.getReg .x2 - c') = t.getMem (e.s.getReg .x2 - c') := by
    rw [hfr₂ _ (by addr_omega [hsp, hbk, hh, hk]) (by addr_omega [hsp, hk]), hm]
  have x9₃ : u₃.getReg .x9 = e.low := by
    rw [b80011408_x9 h₃, e2₂]; rv_eval []; rw [hslot₂ 1800 (by decide)]; exact he.c168
  have x18₃ : (u₃.getReg .x18).toNat = 2 ^ e.m := by
    rw [b80011408_x18 h₃, e2₂]; rv_eval []; rw [hslot₂ 1808 (by decide)]; exact he.c160
  have hs3 : u₃.getMem (e.s.getReg .x2 - 1792) = t.getMem (e.s.getReg .x2 - 1792) := by
    rw [hfr₃ _ (by addr_omega [hsp]) (by addr_omega [hsp]),
      hfr₂ _ (by addr_omega [hsp, hbk, hh]) (by addr_omega [hsp]), hm]
  have x19₃ : (u₃.getReg .x19).toNat = e.pe i := by
    rw [b80011408_x19 h₃, e2₂]; rv_eval []; rw [hold₂ 1792 (by decide)]; exact hb.s3
  have m200 := b800113d0_m_x2_200 h₂
  have m192 := b800113d0_m_x2_192 h₂
  rw [hu2] at m200 m192
  rv_eval [] at m200 m192
  have x10₃ : u₃.getReg .x10 = e.bytesPtr + BitVec.ofNat 64 (2 * (b + 1)) := by
    rw [b80011408_x10 h₃, e2₂]; rv_eval []
    rw [m200, hreg .x10 (by decide), hb.x10, BitVec.add_assoc,
      show (2 : Word) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]
  have hx11 := hb.x11
  have x11₃ : u₃.getReg .x11 = t.getReg .x11 - 2 := by
    rw [b80011408_x11 h₃, e2₂]; rv_eval []; rw [m192, hreg .x11 (by decide)]
  have hbuck₃ : eListAt u₃ e.bk 2048 = (e.bf i (b + 1 - (e.st i).bytesStart)).1 := by
    rw [buckets_congr he fun a ha ↦ hfr₃ a (by addr_omega [ha, hsp, hbk, hh])
      (by addr_omega [ha, hsp, hbk, hh]), hbuck₂, buckets_congr he fun a _ ↦ hm a, hb.buckets,
      bf_succ e hb.blo hbl, hcdef]
    rfl
  have hsum₃ : eListAt u₃ (e.s.getReg .x2 - 1688) 64 =
      (e.bf i (b + 1 - (e.st i).bytesStart)).2 := by
    have h1 : eListAt u₂ (e.s.getReg .x2 - 1688) 64 = eListAt t (e.s.getReg .x2 - 1688) 64 :=
      (eListAt_congr fun n hn j hj ↦ hfr₂ _ (by addr_omega [hn, hj, hsp, hbk, hh])
        (by addr_omega [hn, hj, hsp])).trans (eListAt_congr fun n _ j _ ↦ hm _)
    have h2 : eListAt u e.bk 2048 = eListAt t e.bk 2048 := buckets_congr he fun a _ ↦ hm a
    rw [hsums, h1, h2, hb.sums, hb.buckets, bf_succ e hb.blo hbl, hcdef]
    rfl
  -- `0x80011608`: registers back, next bucket or done
  have e2₃ : u₃.getReg .x2 = e.s.getReg .x2 - 1968 := (k₃ .x2 (by decide)).trans e2₂
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80011608_spec (b80011408_pc h₃) (by
    rv_eval [e2₃]; and_intros <;> valid_access hst [hsp])
  have k₄ := b80011608_keeps h₄
  have hm₄ := b80011608_mem_same h₄
  have hregs : Regs e u₄ := {
    sp := (k₄ .x2 (by decide)).trans e2₃
    mem := hm₃.same hm₄
    x9 := (k₄ .x9 (by decide)).trans x9₃
    x18 := by rw [k₄ .x18 (by decide)]; exact x18₃
    x20 := by rw [b80011608_x20 h₄, e2₃]; rv_eval []; rw [hslot 1816]; exact he.c152
    x21 := by rw [b80011608_x21 h₄, e2₃]; rv_eval []; rw [hslot 1824]; exact he.c144
    x23 := by rw [b80011608_x23 h₄, e2₃]; rv_eval [] }
  have hr := hr.trans (hr₂.trans (hr₃.trans hr₄))
  have hbe := hb.bhi
  by_cases hlast : b + 1 = (e.blk i).bytesEnd
  · have h0 : u₃.getReg .x11 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [x11₃, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
        rw [hx11]; simp only [Sym.wordToNatLit]; omega)), hx11]
      simp only [Sym.wordToNatLit]; omega
    refine ⟨u₄, hr, Or.inr (Or.inr ⟨b80011608_pc_not_taken h₄ h0, ?_⟩)⟩
    exact { hregs with
      lt := hb.lt
      ptr := by rw [hm₄, hold 1848 (by decide)]; exact hb.ptr
      next := by rw [hm₄, hold 1896 (by decide)]; exact hb.next
      we := by rw [hm₄, hold 1888 (by decide)]; exact hb.we
      be := by rw [hm₄, hold 1856 (by decide)]; exact hb.be
      total := by
        rw [hm₄, hm₄, hm₄, hold 1880 (by decide), hold 1872 (by decide), hold 1864 (by decide)]
        exact hb.total
      x19 := by rw [k₄ .x19 (by decide)]; exact x19₃
      blo := Nat.le_of_lt (Nat.lt_of_le_of_lt hb.blo hbe)
      bend := hb.bend
      buckets := by
        rw [buckets_congr he fun a _ ↦ hm₄ a, ← hlast, hbuck₃]
      sums := by
        rw [eListAt_congr fun n _ j _ ↦ hm₄ _, ← hlast, hsum₃] }
  · have h0 : u₃.getReg .x11 ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      rw [x11₃, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
        rw [hx11]; simp only [Sym.wordToNatLit]; omega)), hx11] at this
      simp only [Sym.wordToNatLit] at this; omega
    refine ⟨u₄, hr, Or.inr (Or.inl ⟨b80011608_pc_taken h₄ h0, ?_⟩)⟩
    exact { hregs with
      lt := hb.lt
      ptr := by rw [hm₄, hold 1848 (by decide)]; exact hb.ptr
      next := by rw [hm₄, hold 1896 (by decide)]; exact hb.next
      we := by rw [hm₄, hold 1888 (by decide)]; exact hb.we
      be := by rw [hm₄, hold 1856 (by decide)]; exact hb.be
      total := by
        rw [hm₄, hm₄, hm₄, hold 1880 (by decide), hold 1872 (by decide), hold 1864 (by decide)]
        exact hb.total
      s3 := by rw [hm₄, hs3]; exact hb.s3
      x19 := by rw [k₄ .x19 (by decide)]; exact x19₃
      blo := Nat.le_succ_of_le hb.blo
      bhi := by omega
      bend := hb.bend
      x10 := (k₄ .x10 (by decide)).trans x10₃
      x11 := by
        rw [k₄ .x11 (by decide), x11₃, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
          rw [hx11]; simp only [Sym.wordToNatLit]; omega)), hx11]
        simp only [Sym.wordToNatLit]; omega
      buckets := by rw [buckets_congr he fun a _ ↦ hm₄ a, hbuck₃]
      sums := by rw [eListAt_congr fun n _ j _ ↦ hm₄ _, hsum₃] }

/-- Block `i`'s buckets, to the end. -/
theorem bk_loop (he : EnvOk e) {t : MachineState} {i b : Nat} (hb : BkInv e t i b)
    (hpc : t.pc = 0x800113c8) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x80011618 ∧ BkDone e u i)) := by
  refine Reaches.loop (fun t ↦ ∃ b, t.pc = 0x800113c8 ∧ BkInv e t i b)
    (fun t ↦ (t.getReg .x11).toNat) _ (fun t ⟨b, hpc, hb⟩ ↦ ?_) t ⟨b, hpc, hb⟩
  obtain ⟨u, hr, hd | ⟨hu, hb'⟩ | ⟨hu, hdn⟩⟩ := bk_body he hb hpc
  · exact Or.inl ⟨u, hr, Or.inl hd⟩
  · refine Or.inr ⟨u, hr, ⟨b + 1, hu, hb'⟩, ?_⟩
    rw [hb'.x11, hb.x11]
    have := hb'.bhi
    omega
  · exact Or.inl ⟨u, hr, Or.inr ⟨hu, hdn⟩⟩

end Rv64Verifier.Proofs.Bytecode.Eval
