/-
  Rv64mc.Proof.Runtime.AllocT

  The bump allocator's `alloc` is total: it returns the block `AllocSpec` describes, or, when no
  block of the size at a multiple of 8 at or above `NEXT` ends within the heap, ends the run with
  the guest's abort (`halt(2)`). The total counterpart of `Alloc.lean`, over the same template and
  link facts, from `halt`'s `Aborts` (`HaltT.lean`). Its load and store of `NEXT` lie in a window
  and are aligned by `Windows` (`nextAddr`, `nextAddr_aligned`), the store over no code
  (`Windows.noCodeAt`), which `rv_autoT` closes from the link fact that the data reference is
  `NEXT`'s address; what is left is the block's arithmetic.

  ## Main definitions

  * `AllocStop`, `AllocSpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.Alloc
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.AllocT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime
open Rv64mc.Gen.VerifierRv64.Bump.AsGlobalAlloc.Alloc (Link tmpl)

variable {env : Env}

/-- Where `alloc` may end the run: `a0 = 2`, and the block of the size `a0` asked for, at the first multiple of 8 at
    or above `NEXT`, would end beyond the heap. -/
def AllocStop (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = 2 ∧ env.heapEnd.toNat < ((env.next m).toNat + 7) / 8 * 8 + (regs .x10).toNat

/-- **The total contract of `alloc`**: `AllocSpec`'s, or the abort when the heap is exhausted. -/
def AllocSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need AllocPre (AllocPost env) (Stop := AllocStop env)

/-- `NEXT` rounded up to a multiple of 8, as the code computes it (`BinOp.eval` unfolded). -/
theorem roundUp_toNat {N : Word} (hN : N.toNat < 2 ^ 63) :
    (((if (N &&& 7#64).ult 1#64 = true then (1 : Word) else 0) + 18446744073709551615#64 &&&
      8#64 - (N &&& 7#64)) + N).toNat = (N.toNat + 7) / 8 * 8 := by
  have hr := Alloc.and7 N
  by_cases h0 : N.toNat % 8 = 0
  · have hz : N &&& 7#64 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hr, h0]; rfl)
    simp only [hz, show (0#64 : Word).ult 1#64 = true by decide, ↓reduceIte,
      show ((1 : Word) + 18446744073709551615#64) = 0#64 by decide, BitVec.zero_and, BitVec.zero_add]
    omega
  · have hlt : (N &&& 7#64).ult 1#64 = false := by
      simp only [BitVec.ult, hr, show (1#64 : Word).toNat = 1 by decide, decide_eq_false_iff_not]
      omega
    simp only [hlt, Bool.false_eq_true, ↓reduceIte,
      show ((0 : Word) + 18446744073709551615#64) = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
    rw [BitVec.toNat_add, BitVec.toNat_sub, hr, show (8#64 : Word).toNat = 8 by decide]
    omega

/-- **`alloc` is total**, with no stack, from `halt`'s `Aborts`. -/
theorem total (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hnext : L.d_NEXT.addr = env.nextAddr) (hend : env.heapEnd = 0x78000000#64)
    (hhalt : Aborts env p L.halt.idx 0) : AllocSpecT env p i 0 := by
  have hd : L.d_NEXT.hi + L.d_NEXT.lo = env.nextAddr := hL.d_NEXT.trans hnext
  rv_autoT hp with [hL, hd] using [hhalt]
  all_goals
    have hN : (m.getMem env.nextAddr).toNat ≤ 0x78000000 := by simpa [Env.next, hend] using hpre_5
    have hS := roundUp_toNat (Nat.lt_of_le_of_lt hN (by decide))
    simp only [hd, BinOp.eval] at hc ⊢
    generalize ((if (m.getMem env.nextAddr &&& 7#64).ult 1#64 = true then (1 : Word) else 0) +
      18446744073709551615#64 &&& 8#64 - (m.getMem env.nextAddr &&& 7#64)) + m.getMem env.nextAddr = S at hS hc ⊢
    have hE : (S + regs .x10).toNat = S.toNat + (regs .x10).toNat := by
      rw [BitVec.toNat_add]
      omega
    have hx : (2013265920#64 : Word).toNat = 0x78000000 := by decide
    simp only [BitVec.le_def, BitVec.lt_def, hx] at hc
  -- the block fits: its end stored in `NEXT`, its start returned
  · exact Alloc.frame_setNext (by show (m.getMem env.nextAddr).toNat ≤ _; omega) (by rw [hend, hx]; omega)
  · exact Alloc.static_setNext hpre_4
  · show (m.getMem env.nextAddr).toNat ≤ _
    omega
  · omega
  · rw [Alloc.next_setNext]
    omega
  -- the heap is exhausted: `halt`
  · show env.heapEnd.toNat < ((m.getMem env.nextAddr).toNat + 7) / 8 * 8 + _
    rw [hend, hx]
    omega

end Rv64mc.Proof.Runtime.AllocT

/-- info: 'Rv64mc.Proof.Runtime.AllocT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.AllocT.total
