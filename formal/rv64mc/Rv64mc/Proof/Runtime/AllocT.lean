/-
  Rv64mc.Proof.Runtime.AllocT

  The bump allocator's `alloc` is total: it returns the block `AllocSpec` describes, or, when no
  block of the size at a multiple of 8 at or above `NEXT` ends within the heap, ends the run with
  the guest's abort (`halt(2)`). The total counterpart of `Alloc.lean`, over the same template and
  link facts, from `halt`'s `Aborts` (`HaltT.lean`). Its load and store of `NEXT` lie in a window
  and are aligned by `Windows` (`nextAddr`, `nextAddr_aligned`), the store over no code
  (`Windows.noCodeAt`).

  ## Main definitions

  * `AllocStop`, `AllocSpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.Alloc
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Tactic.TStep

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

/-- `NEXT` rounded up to a multiple of 8, as the code computes it after `tnorm`. -/
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
  intro Q ret top rest regs m hpre hstop hk
  have ⟨⟨⟨hra, hsp⟩, hstk, hst, hnx, hsz, hal⟩, hwin⟩ := hpre
  have hd : L.d_NEXT.hi + L.d_NEXT.lo = env.nextAddr := hL.d_NEXT.trans hnext
  have hN : (m.getMem env.nextAddr).toNat ≤ 0x78000000 := by
    simpa [Env.next, hend] using hnx
  have hS := roundUp_toNat (Nat.lt_of_le_of_lt hN (by decide))
  have hin : inWindow env.nextAddr 8 = true := hwin.nextAddr (by omega)
  have hsz' : (regs .x10).toNat < 2 ^ 63 := hsz
  tsteps hp
  refine TotalRv.ld8 hp rfl (by simpa [Expr.eval, BinOp.eval, updReg_apply, hd] using hin)
    (by simpa [Expr.eval, BinOp.eval, updReg_apply, hd] using hwin.nextAddr_aligned) ?_
  tsteps hp
  simp only [hd]
  generalize ((if (m.getMem env.nextAddr &&& 7#64).ult 1#64 = true then (1 : Word) else 0) +
    18446744073709551615#64 &&& 8#64 - (m.getMem env.nextAddr &&& 7#64)) + m.getMem env.nextAddr = S at hS ⊢
  have hE : (S + regs .x10).toNat = S.toNat + (regs .x10).toNat := by
    rw [BitVec.toNat_add]
    omega
  have hx : (2013265920#64 : Word).toNat = 0x78000000 := by decide
  tcond hp as hc
  -- the block fits: store its end in `NEXT` and return its start
  · have hfit : S.toNat + (regs .x10).toNat ≤ 0x78000000 := by omega
    tsteps hp
    refine TotalRv.sd8 hp rfl (by simpa [Expr.eval, BinOp.eval, updReg_apply, hd] using hin)
      (by simpa [Expr.eval, BinOp.eval, updReg_apply, hd] using hwin.nextAddr_aligned)
      (by simpa [Expr.eval, BinOp.eval, updReg_apply, hd] using hwin.noCodeAt hin (by decide)) ?_
    simp only [Expr.eval, BinOp.eval, updReg_apply, reduceCtorEq, ↓reduceIte, hd]
    tsteps hp
    refine TotalRv.ret hp rfl (by simp [updReg_apply, hra]) (by simp [updReg_apply, hsp]) ?_
    refine hk _ _ ⟨⟨?_, Alloc.frame_setNext ?_ ?_, Alloc.static_setNext hst, ?_, ?_, ?_⟩, rfl⟩
    · simp (disch := decide) only [AbiRegs.updReg_iff]
      exact AbiRegs.refl hsp
    · show (m.getMem env.nextAddr).toNat ≤ _
      omega
    · rw [hend, hx]
      omega
    · show (m.getMem env.nextAddr).toNat ≤ _
      simp only [updReg_apply, reduceCtorEq, ↓reduceIte]
      omega
    · simp only [updReg_apply, reduceCtorEq, ↓reduceIte]
      omega
    · simp only [updReg_apply, reduceCtorEq, ↓reduceIte, Alloc.next_setNext]
      omega
  -- the heap is exhausted: `halt`
  · tsteps hp
    refine Aborts.call hhalt hpre hp rfl (callee_site hL.halt hL.s0 (by simp [updReg_apply]))
      (by simp [updReg_apply, hsp]) fun fr st r' m' h2 ha => hstop fr st r' m' ⟨h2, ?_⟩ ha
    show env.heapEnd.toNat < ((m.getMem env.nextAddr).toNat + 7) / 8 * 8 + (regs .x10).toNat
    rw [hend, hx]
    omega

end Rv64mc.Proof.Runtime.AllocT

/-- info: 'Rv64mc.Proof.Runtime.AllocT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.AllocT.total
