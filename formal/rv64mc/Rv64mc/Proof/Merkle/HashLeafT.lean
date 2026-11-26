/-
  Rv64mc.Proof.Merkle.HashLeafT

  `hash_leaf` is total (`specT`): from the digest's slot (`out`, `a0`) in a window apart from the stack below the
  stack pointer and the leaf's `K` words (`a1`, `a2`), unless there are none, allocated before (`Live`, the partial
  spec's `HashLeaf.Pre`) and in a window, it returns, writing at most the slot's doublewords besides its stack and the
  byte buffer it allocates (`DigestOut`), or ends the run with `a0 = 2` (the allocator out of heap). Safety only: the
  digest written is `keccak_hash`'s, whose functional contract is not total (`KeccakHashSafeT`).

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Hash.KeccakHashT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.PanicsT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Spec.Merkle.Merkle
import Rv64mc.Tactic.SymT
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Multilinear.Heap
import Rv64mc.Gen.Tmpl.Verifier.Merkle.HashLeaf

namespace Rv64mc.Proof.Merkle.HashLeafT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Merkle.HashLeaf (Link tmpl)

/-- The total precondition: the slot in a window and apart from the stack below the stack pointer; the leaf's words,
    unless there are none, allocated before and in a window. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) Layouts.Digest.byteSize ∧ OffStack env (regs .x2) (regs .x10) Layouts.Digest.byteSize ∧
    ((regs .x12).toNat = 0 ∨
      (env.Live m (regs .x11) (8 * (regs .x12).toNat) ∧ InWin env (regs .x11) (8 * (regs .x12).toNat)))

/-- **The total contract of `hash_leaf`**: it returns, writing at most the slot's doublewords, or ends the run with
    `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) (fun regs _ => Spec.Hash.DigestOut (regs .x10))
    (Stop := AbortStop)

/-- The byte vector's header in the frame (at `top - 80`), as `vecCap`, `vecPtr` and `vecLen` name its words. -/
theorem hdr_eq (M : MachineState) (top : Word) :
    vecCap M (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551536#64) ∧
      vecPtr M (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551544#64) ∧
      vecLen M (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551552#64) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [vecCap, vecPtr, vecLen, Layouts.Vec.cap, Layouts.Vec.ptr, Layouts.Vec.len,
    BitVec.add_assoc] <;> rfl

set_option hygiene false in
/-- `reserve`'s `out` (the header's capacity and pointer) lies in the frame below the stack top. -/
local macro "grow_in" : tactic => `(tactic| (
  simp only [GrowOut, rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, Lprog.updReg_apply,
    Tactic.rf, reduceCtorEq, ↓reduceIte, BitVec.add_zero] at hb
  rcases hb with rfl | rfl
  · exact ⟨by rw [hsp]; omega, by rw [hsp]; omega⟩
  · rw [show (top + 18446744073709551536#64 + BitVec.ofNat 64 8 : Word) = top + 18446744073709551544#64 by
      rw [BitVec.add_assoc]; rfl]
    have : (top + 18446744073709551544#64).toNat = top.toNat - 72 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact ⟨by rw [this]; omega, by rw [this]; omega⟩))

set_option hygiene false in
/-- A saved register's slot, kept by `reserve` (call `k`; its `out` is the header) and read through the prologue's
    stores. -/
local macro "slot_r" k:num : tactic => `(tactic| (
  rw [$(Lean.mkIdent (Lean.Name.mkSimple s!"keep{k.getNat}_1")) _
    (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) (by
      simp only [GrowOut, rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, Lprog.updReg_apply,
        Tactic.rf, reduceCtorEq, ↓reduceIte, BitVec.add_zero, BitVec.add_assoc, not_or]
      exact ⟨fun h => absurd ((BitVec.add_right_inj top).1 h) (by decide),
        fun h => absurd ((BitVec.add_right_inj top).1 h) (by decide)⟩)]
  simp (disch := decide) only [Transcript.getMem_setMem_off, MachineState.getMem_setMem_eq]))

/-- A slot of the frame below the stack top is not `NEXT`'s word. -/
theorem slot_ne_next {env : Env} {top c : Word} (hs : env.stackLimit.toNat ≤ (top + c).toNat) :
    top + c ≠ env.nextAddr := fun h => by
  have := env.layout
  rw [h] at hs
  omega

/-- A buffer of doublewords below a word misses it. -/
theorem not_dwordsOf {q a : Word} {n : Nat} (hq : q.toNat % 8 = 0) (h : q.toNat + n ≤ a.toNat) :
    ¬ DwordsOf q n a := by
  simp only [DwordsOf, InRange, toNat_alignToDword]
  omega

set_option hygiene false in
/-- A saved register's slot after the copy (call 8): kept by `memcpy` (its `out` is the buffer, in the heap), by
    `reserve` (call 6) and by `alloc` (call 5), read through the prologue's stores. -/
local macro "slot_w" : tactic => `(tactic| (
  rw [keep8_1 _ (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) (by
    simp only [CopyOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    exact not_dwordsOf hret5_17 (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
  slot_r 6
  rw [keep5_1 _ (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
  simp (disch := decide) only [Transcript.getMem_setMem_off, MachineState.getMem_setMem_eq]))

/- Both paths (no words, and the words copied) through four calls in one run: the default heartbeats do not cover
   it. -/
set_option maxHeartbeats 400000 in
set_option rv_sym.heap true in
/-- **`hash_leaf` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needH needR needC needK : Nat} (hnA : 80 + needA ≤ need) (hnH : 80 + needH ≤ need)
    (hnR : 80 + needR ≤ need) (hnC : 80 + needC ≤ need) (hnK : needK ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hhe : Aborts env p L.handleError.idx needH)
    (hres : Runtime.ReserveT.ReserveSpecT env 1 1 p L.reserve.idx needR)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC)
    (hkh : Hash.KeccakHashT.KeccakHashSafeT env p L.keccakHash.idx needK) : specT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hhe, hres, hcp, hkh]
  all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero,
    Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
  all_goals try simp (disch := decide) only [Transcript.getMem_setMem_off, MachineState.getMem_setMem_eq]
  all_goals try rv_closeT
  all_goals try first | exact absurd hc_1 hc | exact absurd hc hc_1
  all_goals
    have hsp : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hshl : (regs .x12 <<< 3).toNat = 8 * (regs .x12).toNat := by
      have := env.layout
      have := hpre_10.top_le
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      rcases hpre_8 with h | ⟨-, h⟩
      · rw [h]
      · unfold InWin at h; omega
  -- no words
  · slot_r 1
  · have hl1 := hret1_16
    simp only [(hdr_eq _ top).2.2] at hl1
    simp (disch := decide) only [MachineState.getMem_setMem_eq] at hl1
    exact .inl (by rw [hl1]; rfl)
  · refine ⟨?_, (Multilinear.frame_call_own ?_ hret1_14 (by rw [hsp]; omega) fun b hb => ?_).trans hret2_14
      (Nat.le_refl _) fun a h => Or.inr (Or.inr (Or.inr h)), hret2_15, trivial⟩
    · simp only [AbiRegs, Tactic.rf, and_true, true_and]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> slot_r 1
    · rv_closeT
    · grow_in
  -- the words
  · rw [hshl]; rcases hpre_8 with h | ⟨-, h⟩
    · exact absurd (BitVec.eq_of_toNat_eq h) hc
    · have := env.layout; have := hpre_10.top_le; unfold InWin at h; omega
  all_goals
    obtain ⟨hlive, hwin⟩ := hpre_8.resolve_left fun h => hc (BitVec.eq_of_toNat_eq h)
    have hH := hret6_16
    have hC := hret6_17
    simp only [(hdr_eq _ top).1, (hdr_eq _ top).2.1, (hdr_eq _ top).2.2] at hH hC
    simp (disch := decide) only [Transcript.getMem_setMem_off, MachineState.getMem_setMem_eq] at hH hC
    obtain ⟨-, hq⟩ := hC (by simp)
    try simp only [hq, hH, BitVec.add_zero, BitVec.zero_add]
    try simp only [hq, hH, BitVec.add_zero] at keep8_1 keep8_2
    have hn5 := hret5_14.2.1
    have hq0 := hret5_16
    have hqn := hret5_18
    have hlay := env.layout
    have hng := hpre_10.next_ge
    have htl := hpre_10.top_le
    rw [hshl] at hqn
    unfold Env.Live at hlive
    have hqs : (r5 .x10).toNat + (regs .x12 <<< 3).toNat ≤ top.toNat - 80 := by rw [hshl]; omega
  all_goals try rv_closeT
  · rw [hshl]
    exact Or.inr ⟨Or.inl ⟨by omega, by omega⟩, Or.inl (by omega), hwin.inWindow hpre_10, Or.inl (by omega)⟩
  · slot_w
  · rw [hshl]
    exact Or.inr ⟨hpre_10.heapObj (by omega) (by omega), Or.inl (by omega)⟩
  · have h72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hn6 : (env.next m5).toNat ≤ (env.next m6).toNat := by
      have h := hret6_14.1
      rwa [Tactic.next_setMem (slot_ne_next (by rw [h64]; omega)), Tactic.next_setMem (slot_ne_next (by
        rw [h72]; omega)), Tactic.next_setMem (slot_ne_next (by rw [hsp]; omega))] at h
    have hn8 := hret8_14.1
    have hF6 : env.Frame top (Spec.Hash.DigestOut (regs .x10)) m m6 := by
      refine Multilinear.frame_call_own (Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot
        (Multilinear.frame_call_own ?_ hret5_14 (by rw [hsp]; omega) fun b hb => hb.elim) (by omega) (by omega))
        (by omega) (by omega)) (by omega) (by omega)) hret6_14 (by rw [hsp]; omega) fun b hb => ?_
      · rv_closeT
      · grow_in
    refine ⟨?_, (hF6.trans hret8_14 (by rw [hsp]; omega) fun a h => Or.inr (Or.inl ?_)).trans hret9_14
      (Nat.le_refl _) fun a h => Or.inr (Or.inr (Or.inr h)), hret9_15, trivial⟩
    · simp only [AbiRegs, Tactic.rf, and_true, true_and]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> slot_w
    · simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
        toNat_alignToDword, hq, hH, BitVec.add_zero, hshl] at h
      have := hret5_17
      omega

end Rv64mc.Proof.Merkle.HashLeafT

/-- info: 'Rv64mc.Proof.Merkle.HashLeafT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Merkle.HashLeafT.total
