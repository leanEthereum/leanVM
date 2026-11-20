/-
  Rv64mc.Proof.Runtime.Alloc

  The bump allocator's `alloc` meets `AllocSpec`: it rounds `NEXT` up to the alignment (`NEXT % align`, then the
  missing part masked to zero when there is none), checks that the block ends within the heap and does not wrap,
  and stores its end in `NEXT`, the one word it writes. Two link-time facts: its data reference is `NEXT`, and the
  heap's end is the literal it compares with.
-/

import Rv64mc.Gen.Tmpl.VerifierRv64.Bump.AsGlobalAlloc.Alloc
import Rv64mc.Spec.Runtime.Alloc
import Rv64mc.Spec.Runtime.Panic

namespace Rv64mc.Proof.Runtime.Alloc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.VerifierRv64.Bump.AsGlobalAlloc.Alloc (Link tmpl)

variable {env : Env}

theorem next_setNext {m : MachineState} {e : Word} : env.next (m.setMem env.nextAddr e) = e := by
  simp [Env.next, MachineState.getMem, MachineState.setMem]

/-- A store into `NEXT` that does not lower it and stays within the heap is in the frame of every call. -/
theorem frame_setNext {top e : Word} {out : Word → Prop} {m : MachineState} (hlo : (env.next m).toNat ≤ e.toNat)
    (hhi : e.toNat ≤ env.heapEnd.toNat) : env.Frame top out m (m.setMem env.nextAddr e) := by
  refine ⟨by rw [next_setNext]; exact hlo, by rw [next_setNext]; exact hhi, fun a ha => ?_⟩
  have : a ≠ env.nextAddr := fun h => ha (Or.inr (Or.inr (Or.inl h)))
  simp [MachineState.getMem, MachineState.setMem, this]

/-- A store into `NEXT` keeps the static data. -/
theorem static_setNext {m : MachineState} {e : Word} (h : env.Static m) : env.Static (m.setMem env.nextAddr e) := by
  refine env.static_frame m _ (fun b _ hb => ?_) h
  have : b ≠ env.nextAddr := fun he => by have := env.layout; rw [he] at hb; omega
  simp [MachineState.getMem, MachineState.setMem, this]

theorem toNat_add_ofNat' {S x : Word} (h : S.toNat + x.toNat < 2 ^ 64) : (S + x).toNat = S.toNat + x.toNat := by
  rw [BitVec.toNat_add]; omega

theorem end_lt {S N x : Nat} (h1 : S ≤ N + 7) (h2 : N ≤ 0x78000000) (h3 : x < 2 ^ 63) : S + x < 2 ^ 64 := by
  omega

theorem and7 (N : Word) : (N &&& 7#64).toNat = N.toNat % 8 := by
  rw [BitVec.toNat_and, show (7#64 : Word).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

/-- `NEXT` rounded up to a multiple of 8, as the code computes it: the missing part `8 - NEXT % 8`, masked to zero
    when there is none. -/
theorem round_up8 {N : Word} (hN : N.toNat < 2 ^ 63) :
    N.toNat ≤ (((if N &&& 7#64 = 0#64 then 1#64 else 0#64) + 0xffffffffffffffff#64 &&& 8#64 + -(N &&& 7#64)) +
      N).toNat ∧
    (((if N &&& 7#64 = 0#64 then 1#64 else 0#64) + 0xffffffffffffffff#64 &&& 8#64 + -(N &&& 7#64)) + N).toNat % 8 =
      0 ∧
    (((if N &&& 7#64 = 0#64 then 1#64 else 0#64) + 0xffffffffffffffff#64 &&& 8#64 + -(N &&& 7#64)) + N).toNat ≤
      N.toNat + 7 := by
  have hr := and7 N
  by_cases h0 : N &&& 7#64 = 0#64
  · simp only [h0, ite_true]
    rw [show (1#64 + 0xffffffffffffffff#64 : Word) = 0#64 by decide, BitVec.zero_and, BitVec.zero_add]
    have : N.toNat % 8 = 0 := by rw [← hr, h0]; rfl
    omega
  · simp only [h0, ite_false]
    rw [show (0#64 + 0xffffffffffffffff#64 : Word) = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
    have hne : N.toNat % 8 ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [hr, h]; rfl))
    have hlt : N.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
    have e : (8#64 + -(N &&& 7#64) + N).toNat = 8 - N.toNat % 8 + N.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_neg, hr, show (8#64 : Word).toNat = 8 by decide]
      omega
    rw [e]
    omega

/-- **The contract of `alloc`**, with no stack, from `halt`'s. -/
theorem ok (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hnext : L.d_NEXT.addr = env.nextAddr) (hend : env.heapEnd = 0x78000000#64)
    (hhalt : NoReturn env p L.halt.idx 0) : AllocSpec env p i 0 := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, hsz, hal⟩ hk
  have hd : L.d_NEXT.hi + L.d_NEXT.lo = env.nextAddr := hL.d_NEXT.trans hnext
  have hN : (m.getMem env.nextAddr).toNat ≤ 0x78000000 := by
    simpa [Env.next, hend] using hnx
  have hN' : (m.getMem env.nextAddr).toNat < 2 ^ 63 := by omega
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hL.halt, hL.s0, hd, Holds.post] using [hhalt.contract]
  -- the return: the block's start `S` and end `S + size`
  · rw [← BitVec.add_assoc] at hc ⊢
    obtain ⟨hS1, hS2, hS3⟩ := round_up8 hN'
    generalize ((if m.getMem env.nextAddr &&& 7#64 = 0#64 then 1#64 else 0#64) + 0xffffffffffffffff#64 &&&
      8#64 + -(m.getMem env.nextAddr &&& 7#64)) + m.getMem env.nextAddr = S at hc hS1 hS2 hS3 ⊢
    have hend' : (S + regs .x10).toNat = S.toNat + (regs .x10).toNat := toNat_add_ofNat' (end_lt hS3 hN hsz)
    have hc2' : (S + regs .x10).toNat ≤ 0x78000000 := Nat.le_trans (BitVec.le_def.mp hc) (by decide)
    apply hk
    refine ⟨?_, frame_setNext ?_ ?_, static_setNext hst, ?_, ?_, ?_⟩
    · simp (disch := decide) only [AbiRegs.updReg_iff]; exact AbiRegs.refl hsp
    · show (m.getMem env.nextAddr).toNat ≤ _
      rw [hend']; exact Nat.le_trans hS1 (Nat.le_add_right _ _)
    · rw [hend]; exact Nat.le_trans hc2' (by decide)
    · show (m.getMem env.nextAddr).toNat ≤ S.toNat
      exact hS1
    · show S.toNat % 8 = 0
      exact hS2
    · show S.toNat + (regs .x10).toNat = (env.next (m.setMem env.nextAddr (S + regs .x10))).toNat
      rw [next_setNext, hend']
  -- `halt`'s precondition
  · exact Holds.pre_call (by show _ ≤ (regs .x2).toNat; rw [hsp]; exact hstk) hst hnx trivial
      (by show (regs .x2).toNat % 16 = 0; rw [hsp]; exact hal)

end Rv64mc.Proof.Runtime.Alloc
