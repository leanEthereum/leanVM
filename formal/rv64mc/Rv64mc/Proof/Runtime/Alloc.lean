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

/-- `NEXT` rounded up to a multiple of `a`, as the code computes it: the remainder, and the missing part masked to
    zero when there is none. -/
theorem round_up {a N : Word} (ha : 0 < a.toNat) (ha' : a.toNat < 2 ^ 63) (hN : N.toNat < 2 ^ 63) :
    N.toNat ≤ (((if N % a = 0#64 then 1#64 else 0#64) + 0xffffffffffffffff#64 &&& a + -(N % a)) + N).toNat ∧
      (((if N % a = 0#64 then 1#64 else 0#64) + 0xffffffffffffffff#64 &&& a + -(N % a)) + N).toNat % a.toNat =
        0 := by
  have hr : (N % a).toNat = N.toNat % a.toNat := BitVec.toNat_umod
  have hrl : N.toNat % a.toNat < a.toNat := Nat.mod_lt _ ha
  by_cases h0 : N % a = 0#64
  · have : N.toNat % a.toNat = 0 := by rw [← hr, h0]; rfl
    simp only [h0, ite_true]
    have e : (1#64 + 0xffffffffffffffff#64 &&& a + -0#64) = 0#64 := by bv_decide
    rw [e, BitVec.zero_add]; omega
  · simp only [h0, ite_false]
    have e : (0#64 + 0xffffffffffffffff#64 &&& a + -(N % a)) = a - N % a := by bv_decide
    have hne : N.toNat % a.toNat ≠ 0 := fun h => h0 (by apply BitVec.eq_of_toNat_eq; rw [hr, h]; rfl)
    have hs : (a - N % a + N).toNat = a.toNat - N.toNat % a.toNat + N.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_sub, hr]; omega
    rw [e, hs]
    refine ⟨by omega, ?_⟩
    have := Nat.mod_add_div N.toNat a.toNat
    rw [show a.toNat - N.toNat % a.toNat + N.toNat = a.toNat * (N.toNat / a.toNat + 1) by
      rw [Nat.mul_add]; omega]
    simp

theorem add_toNat_of_le {S x : Word} (h : S ≤ S + x) : (S + x).toNat = S.toNat + x.toNat := by
  rw [BitVec.le_def, BitVec.toNat_add] at h; rw [BitVec.toNat_add]; omega

/-- **The contract of `alloc`**, with no stack, from `halt`'s. -/
theorem ok (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hnext : L.d_NEXT.addr = env.nextAddr) (hend : env.heapEnd = 0x78000000#64)
    (hhalt : NoReturn env p L.halt.idx 0) : AllocSpec env p i 0 := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, hal, hal'⟩ hk
  have hd : L.d_NEXT.hi + L.d_NEXT.lo = env.nextAddr := hL.d_NEXT.trans hnext
  have hN : (m.getMem env.nextAddr).toNat ≤ 0x78000000 := by
    simpa [Env.next, hend] using hnx
  have ha0 : regs .x10 ≠ 0#64 := fun h => by rw [h] at hal; simp at hal
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hL.halt, hL.s0, hd, Holds.post, ha0] using [hhalt.contract]
  -- the return: the block's start `S` and end `S + size`
  · rw [← BitVec.add_assoc] at hc ⊢
    obtain ⟨hS1, hS2⟩ := round_up hal hal' (by omega : (m.getMem env.nextAddr).toNat < 2 ^ 63)
    generalize ((if m.getMem env.nextAddr % regs .x10 = 0#64 then 1#64 else 0#64) + 0xffffffffffffffff#64 &&&
      regs .x10 + -(m.getMem env.nextAddr % regs .x10)) + m.getMem env.nextAddr = S at hc hS1 hS2 ⊢
    obtain ⟨hc1, hc2⟩ := hc
    have hend' : (S + regs .x11).toNat = S.toNat + (regs .x11).toNat := add_toNat_of_le hc1
    have hc2' : (S + regs .x11).toNat ≤ 0x78000000 := Nat.le_trans (BitVec.le_def.mp hc2) (by decide)
    apply hk
    refine ⟨?_, frame_setNext ?_ ?_, static_setNext hst, ?_, ?_, ?_⟩
    · simp (disch := decide) only [AbiRegs.updReg_iff]; exact AbiRegs.refl hsp
    · show (m.getMem env.nextAddr).toNat ≤ _
      rw [hend']; exact Nat.le_trans hS1 (Nat.le_add_right _ _)
    · rw [hend]; exact Nat.le_trans hc2' (by decide)
    · show (m.getMem env.nextAddr).toNat ≤ S.toNat
      exact hS1
    · show S.toNat % (regs .x10).toNat = 0
      exact hS2
    · show S.toNat + (regs .x11).toNat = (env.next (m.setMem env.nextAddr (S + regs .x11))).toNat
      rw [next_setNext, hend']
  -- `halt`'s precondition
  · exact Holds.pre_call (by show _ ≤ (regs .x2).toNat; rw [hsp]; exact hstk) hst hnx trivial

end Rv64mc.Proof.Runtime.Alloc
