import Rv64Verifier.Proofs.Bytecode.EvalCredit

/-!
# `Bytecode::evaluate`: a block's bit sums, zeroed

`0x8001136c` reloads the block's pointer and saves the next one's; `0x80011380` zeroes
`bit_sums` (64 `E`s at `sp + 280`), an `E` per iteration (`zero_loop`).
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

variable {e : Env}

/-- What the bucket phase may write: the next block's pointer, `bytes_end`, the slots from
`sp + 176` to the bit sums' end, and the buckets. -/
@[rv_addr] def BkW (e : Env) (a : Word) : Prop :=
  Within a (e.s.getReg .x2 - 1896) 8 ∨ Within a (e.s.getReg .x2 - 1856) 8 ∨
    Within a (e.s.getReg .x2 - 1792) 1640 ∨ Within a e.bk 49152

/-- `Blk` over a step that writes only in `BkW` and keeps the registers it names. -/
theorem Blk.of_mem (he : EnvOk e) {t t' : MachineState} {i : Nat} (hb : Blk e t i)
    (hm : ∀ a, ¬ BkW e a → t'.getMem a = t.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x9, .x11, .x18, .x20, .x21, .x23], t'.getReg r = t.getReg r) :
    Blk e t' i := by
  have hsp := he.sp
  have hbk := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hbk hh
  exact {
    sp := (hr .x2 (by decide)).trans hb.sp
    mem := hb.mem.frame fun a ha ↦ hm a fun hw ↦ ha (by addr_omega [hw, hsp])
    x9 := (hr .x9 (by decide)).trans hb.x9
    x18 := by rw [hr .x18 (by decide)]; exact hb.x18
    x20 := (hr .x20 (by decide)).trans hb.x20
    x21 := (hr .x21 (by decide)).trans hb.x21
    x23 := (hr .x23 (by decide)).trans hb.x23
    lt := hb.lt
    ptr := by rw [hm _ (by addr_omega [hsp, hbk, hh])]; exact hb.ptr
    we := by rw [hm _ (by addr_omega [hsp, hbk, hh])]; exact hb.we
    total := by
      rw [hm _ (by addr_omega [hsp, hbk, hh]), hm _ (by addr_omega [hsp, hbk, hh]),
        hm _ (by addr_omega [hsp, hbk, hh])]
      exact hb.total
    bs := by rw [hr .x11 (by decide)]; exact hb.bs
    wsle := hb.wsle
    wele := hb.wele }

/-- Zeroing the bit sums, before entry `k` (`0x80011380`). -/
structure ZInv (e : Env) (t : MachineState) (i k : Nat) : Prop extends Mid e t i where
  next : t.getMem (e.s.getReg .x2 - 1896) = e.blocksPtr + BitVec.ofNat 64 (24 * (i + 1))
  x13 : t.getReg .x13 = e.blocksPtr + BitVec.ofNat 64 (24 * i)
  x12 : t.getReg .x12 = e.s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * k)
  x10 : t.getReg .x10 = e.s.getReg .x2 - 152
  klt : k < 64
  zero : ∀ n < k, eAt t (e.s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * n)) = 0

/-- After zeroing (`0x80011394`). -/
structure ZDone (e : Env) (t : MachineState) (i : Nat) : Prop extends Mid e t i where
  next : t.getMem (e.s.getReg .x2 - 1896) = e.blocksPtr + BitVec.ofNat 64 (24 * (i + 1))
  x13 : t.getReg .x13 = e.blocksPtr + BitVec.ofNat 64 (24 * i)
  zero : eListAt t (e.s.getReg .x2 - 1688) 64 = List.replicate 64 0

/-- `Mid` over a step that writes only in `BkW` but the buckets, keeping the named registers. -/
theorem Mid.of_mem (he : EnvOk e) {t t' : MachineState} {i : Nat} (hb : Mid e t i)
    (hm : ∀ a, ¬ BkW e a → t'.getMem a = t.getMem a)
    (hbk : ∀ a, Within a e.bk 49152 → t'.getMem a = t.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x9, .x11, .x18, .x19, .x20, .x21, .x23], t'.getReg r = t.getReg r) :
    Mid e t' i :=
  { hb.toBlk.of_mem he hm fun r hr' ↦ hr r (mem_of_mem hr' _) with
    x19 := by rw [hr .x19 (by decide)]; exact hb.x19
    buckets := (buckets_congr he hbk).trans hb.buckets }

set_option maxHeartbeats 2000000 in
/-- `0x8001136c`: the block's pointer back, the next one's saved, the zeroing set up. -/
theorem zero_start (he : EnvOk e) {t : MachineState} {i : Nat} (hm : Mid e t i)
    (hpc : t.pc = 0x8001136c) :
    ∃ u, Reaches Image.code t u ∧ u.pc = 0x80011380 ∧ ZInv e u i 0 := by
  have hsp := he.sp
  have hbk := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hbk hh
  have hst := he.pre.stack.valid
  have e2 : t.getReg .x2 = e.s.getReg .x2 - 1968 := hm.sp
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b8001136c_spec hpc (by
    rv_eval [e2]; and_intros <;> valid_access hst [hsp])
  have k := b8001136c_keeps h
  have hf := b8001136c_frame h (by rw [e2]; addr_omega [hsp])
  rw [e2] at hf
  have m72 := b8001136c_m_x2_72 h
  have x13 := b8001136c_x13 h
  rw [e2] at m72 x13
  rv_eval [] at m72 x13
  have hptr := hm.ptr
  refine ⟨u, hr, b8001136c_pc h, ?_⟩
  exact { hm.of_mem he (fun a ha ↦ hf a (by addr_omega [ha, hsp])) (fun a ha ↦ hf a (by
      addr_omega [ha, hsp, hbk, hh])) (fun r hr' ↦ k r (mem_of_mem hr' _)) with
    next := by
      rw [m72, hptr, BitVec.add_assoc]
      congr 1
      rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]
    x13 := x13.trans hptr
    x12 := by rw [b8001136c_x12 h, e2]; rv_eval [Nat.reduceMul]
    x10 := by rw [b8001136c_x10 h, e2]; rv_eval []
    klt := by decide
    zero := fun n hn ↦ absurd hn (Nat.not_lt_zero _) }

set_option maxHeartbeats 2000000 in
/-- One entry zeroed. -/
theorem zero_body (he : EnvOk e) {t : MachineState} {i k : Nat} (hz : ZInv e t i k)
    (hpc : t.pc = 0x80011380) :
    ∃ u, Reaches Image.code t u ∧ ((u.pc = 0x80011380 ∧ ZInv e u i (k + 1)) ∨
      (u.pc = 0x80011394 ∧ ZDone e u i)) := by
  have hsp := he.sp
  have hbk := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hbk hh
  have hst := he.pre.stack.valid
  have hk := hz.klt
  have x12 := hz.x12
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b80011380_spec hpc (by
    rv_eval [x12]; and_intros <;> valid_access hst [hsp, hk])
  have kk := b80011380_keeps h
  have hf := b80011380_frame h (by rw [x12]; addr_omega [hsp, hk])
  rw [x12] at hf
  have z0 := b80011380_m_x12_0 h
  have z1 := b80011380_m_x12_8 h
  have z2 := b80011380_m_x12_16 h
  rw [x12] at z0 z1 z2
  have hmid : Mid e u i := hz.toMid.of_mem he (fun a ha ↦ hf a (by addr_omega [ha, hsp, hk]))
    (fun a ha ↦ hf a (by addr_omega [ha, hsp, hk, hbk, hh])) (fun r hr' ↦ kk r (mem_of_mem hr' _))
  have hzero : ∀ n < k + 1, eAt u (e.s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * n)) = 0 := by
    intro n hn
    by_cases hnk : n = k
    · subst hnk
      apply eAt_eq_of_limbs
      rw [z0, z1, z2]
      decide +kernel
    · rw [← hz.zero n (by omega)]
      unfold eAt
      rw [hf _ (by addr_omega [hsp, hk, hn, hnk]), hf _ (by addr_omega [hsp, hk, hn, hnk]),
        hf _ (by addr_omega [hsp, hk, hn, hnk])]
  have hnext : u.getMem (e.s.getReg .x2 - 1896) = e.blocksPtr + BitVec.ofNat 64 (24 * (i + 1)) :=
    (hf _ (by addr_omega [hsp, hk])).trans hz.next
  have hx13 : u.getReg .x13 = e.blocksPtr + BitVec.ofNat 64 (24 * i) :=
    (kk .x13 (by decide)).trans hz.x13
  by_cases hl : k + 1 = 64
  · refine ⟨u, hr, Or.inr ⟨b80011380_pc_not_taken h (by
      rw [x12, hz.x10, BitVec.add_assoc]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Sym.wordToNatLit]
      simp only [evalStack, eqKernelStack, mulStack, heapEnd] at hsp
      omega), ?_⟩⟩
    exact { hmid with
      next := hnext
      x13 := hx13
      zero := by
        apply List.ext_getElem (by simp [eListAt_length])
        intro n h1 _
        rw [eListAt_getElem, List.getElem_replicate]
        rw [eListAt_length] at h1
        exact hzero n (by omega) }
  · refine ⟨u, hr, Or.inl ⟨b80011380_pc_taken h (by
      rw [x12, hz.x10, BitVec.add_assoc]
      intro heq
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Sym.wordToNatLit] at this
      simp only [evalStack, eqKernelStack, mulStack, heapEnd] at hsp
      omega), ?_⟩⟩
    exact { hmid with
      next := hnext
      x13 := hx13
      x12 := by
        rw [b80011380_x12 h, x12, BitVec.add_assoc,
          show (24 : Word) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]
      x10 := (kk .x10 (by decide)).trans hz.x10
      klt := by omega
      zero := hzero }

/-- The bit sums zeroed. -/
theorem zero_loop (he : EnvOk e) {t : MachineState} {i : Nat} (hm : Mid e t i)
    (hpc : t.pc = 0x8001136c) :
    ∃ u, Reaches Image.code t u ∧ u.pc = 0x80011394 ∧ ZDone e u i := by
  obtain ⟨u, hr, hu, hz⟩ := zero_start he hm hpc
  obtain ⟨v, hv, hd⟩ := Reaches.loop (fun t ↦ ∃ k, t.pc = 0x80011380 ∧ ZInv e t i k)
    (fun t ↦ 64 - ((t.getReg .x12).toNat - ((e.s.getReg .x2).toNat - 1688)) / 24)
    (fun t ↦ t.pc = 0x80011394 ∧ ZDone e t i) (fun t ⟨k, hpc, hz⟩ ↦ by
      obtain ⟨w, hw, ⟨hwp, hz'⟩ | hd⟩ := zero_body he hz hpc
      · refine Or.inr ⟨w, hw, ⟨k + 1, hwp, hz'⟩, ?_⟩
        have hsp := he.sp
        have ht : ∀ k ≤ 64, (e.s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * k)).toNat =
            (e.s.getReg .x2).toNat - 1688 + 24 * k := fun k hk ↦ by addr_omega [hsp, hk]
        have := hz'.klt
        rw [hz'.x12, hz.x12, ht _ (by omega), ht _ (by omega)]
        omega
      · exact Or.inl ⟨w, hw, hd⟩) u ⟨0, hu, hz⟩
  exact ⟨v, hr.trans hv, hd⟩

end Rv64Verifier.Proofs.Bytecode.Eval
