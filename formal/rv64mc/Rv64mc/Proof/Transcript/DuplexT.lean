/-
  Rv64mc.Proof.Transcript.DuplexT

  `Sponge::duplex` is total (`specT`): from a sponge `SpongeT` (`SpongeReprT`) that its caller owns (`Owned`: below
  `NEXT` or in a caller's frame), it returns with the sponge `SpongeT` again, writing nothing outside it and its
  stack, or ends the run with `a0 = 2` on more than four waiting scalars (`slice_index_fail`). Safety only: the
  permuted lanes are the partial contract's (`Duplex.lean`), over `keccak_f`'s functional contract, which is not total.
  The body is cut where the waiting scalars are read (instruction 32) and where their lanes meet before the
  permutation (instruction 100); each part starts from the frame invariant `TailInv` (the registers kept, the frame
  of the stack stores, the code, the static data and the saved registers' slots).

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `TailInv`

  ## Main results

  * `getMem_owned`, `tail_ok`, `mid_ok`, `total`
-/

import Rv64mc.Proof.Transcript.SpongeReprT
import Rv64mc.Proof.Hash.KeccakFT
import Rv64mc.Proof.Runtime.MemsetBytesT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Spec.Transcript.Duplex
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Sponge.Duplex

namespace Rv64mc.Proof.Transcript.DuplexT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Transcript.SpongeReprT
open Rv64mc.Gen.Verifier.Transcript.Sponge.Duplex (Link tmpl)

/-- The total precondition: the sponge `SpongeT`, and owned by the caller (below `NEXT`, or at or above the stack
    pointer). -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SpongeT env m (regs .x10) ∧ env.Owned m (regs .x2) (regs .x10) 328

/-- The total postcondition: the sponge `SpongeT` again. -/
def PostT (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x10)

/-- **The total contract of `Sponge::duplex`**: `PreT` to `PostT`, writing at most the sponge, or ending the run with
    `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) Rv64mc.Spec.Transcript.Duplex.Out (Stop := AbortStop)

/-- A word an `Owned` object starts with is kept by a frame that writes only below the stack pointer. -/
theorem getMem_owned {env : Env} {top a : Word} {n : Nat} {m M : MachineState} (hf : env.Frame top Tactic.F m M)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat ≤ top.toNat)
    (ho : env.Owned m top a n) (hn : 0 < n) : M.getMem a = m.getMem a := by
  rcases ho.1 with h | h
  · exact hf.getMem_below_next hnx (by omega) id
  · exact Tactic.frame_above hf hlim a (BitVec.le_def.2 h)

/-- The state at instruction 32 (the waiting scalars' count read) and at 100 (the permutation's call): the sponge's
    pointer and its state's, the saved registers, the frame of the stack stores, the code, the static data, the saved
    registers' slots. -/
def TailInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551392#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x10 + 24#64 ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9

set_option rv_sym.heap true in
/-- From the permutation's call: `keccak_f`, the copy back, `n_pending` cleared, the return. -/
theorem tail_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC needK : Nat} (hnC : 224 + needC ≤ need) (hnK : 224 + needK ≤ need)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC)
    (hkf : Hash.KeccakFT.KeccakFSafeT env p L.keccakF.idx needK)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) Rv64mc.Spec.Transcript.Duplex.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hs : SpongeT env m (regs .x10)) (ho : env.Owned m top (regs .x10) 328) :
    ∀ R M, TailInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 100, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨ha8, hw, hn4, hg⟩ := hs
  rv_introT hinv
  rv_symT hp with [hL, (by omega : env.stackLimit.toNat + 224 ≤ top.toNat), hW.top_le,
    (rfl : Spec.Hash.KeccakF.stateBytes = 200), (by decide : (200#64).toNat = 200)] using [hcp, hkf]
  · have h24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by unfold InWin at hw; omega)
    have hsp : (top + 18446744073709551392#64).toNat = top.toNat - 224 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have := hW.top_le
    have := ho.1
    have := env.layout
    have := hW.nextAddr_ge
    unfold InWin at hw
    simp only [OffStack, inWindow_iff, h24, hsp, show (200#64).toNat = 200 from rfl]
    refine Or.inr ⟨by omega, by omega, by omega, by omega⟩
  · have hMa := getMem_owned hinv_14 hnx (by omega) ho (by decide)
    have hsp : (top + 18446744073709551392#64).toNat = top.toNat - 224 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have := ho.1
    have := hinv_14.1
    have := hret1_14.1
    have := env.layout
    have h24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by unfold InWin at hw; omega)
    rw [keep2_2 _ (by omega) (by
        simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
          toNat_alignToDword, h24, BitVec.toNat_ofNat]
        omega),
      keep1_2 _ (by omega) (by
        simp only [Spec.Hash.KeccakF.Out, Spec.Hash.KeccakF.stateBytes, InRange, Lprog.updReg_apply, Tactic.rf,
          reduceCtorEq, ↓reduceIte, hsp]
        omega), hMa]
    exact hg

set_option rv_sym.heap true in
/-- From the waiting scalars' count: their lanes written into the buffer, on each of the five counts. -/
theorem mid_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC needK needF : Nat} (hnC : 224 + needC ≤ need) (hnK : 224 + needK ≤ need)
    (hnF : 224 + needF ≤ need)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC)
    (hkf : Hash.KeccakFT.KeccakFSafeT env p L.keccakF.idx needK)
    (hfail : Aborts env p L.sliceIndexFail.idx needF)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostT env) Rv64mc.Spec.Transcript.Duplex.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hs : SpongeT env m (regs .x10)) (ho : env.Owned m top (regs .x10) 328) :
    ∀ R M, TailInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 32, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  rv_introT hinv
  rv_symT hp stop [100] with [hL, (by omega : env.stackLimit.toNat + 224 ≤ top.toNat), hW.top_le] using [hfail]
  all_goals
    refine tail_ok env p i L hp hL hnC hnK hcp hkf hk hstk hst hnx hal hW hs ho _ _ ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rv_closeT

set_option rv_sym.heap true in
/-- **`Sponge::duplex` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needS needK needF : Nat} (hnC : 224 + needC ≤ need) (hnS : 224 + needS ≤ need)
    (hnK : 224 + needK ≤ need) (hnF : 224 + needF ≤ need)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC)
    (hset : Runtime.MemsetBytesT.MemsetSpecT env p L.memset.idx needS)
    (hkf : Hash.KeccakFT.KeccakFSafeT env p L.keccakF.idx needK)
    (hfail : Aborts env p L.sliceIndexFail.idx needF) : specT env p i need := by
  rv_autoT hp stop [32] with [hL, (by omega : env.stackLimit.toNat + 224 ≤ top.toNat), hpre_13.top_le,
    (by decide : (200#64).toNat = 200)] using [hcp, hset]
  · obtain ⟨ha8, hw, hn4, hg⟩ := And.intro hpre_6 (And.intro hpre_7 (And.intro hpre_8 hpre_9))
    have h24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by omega)
    have hsp : (top + 18446744073709551392#64).toNat = top.toNat - 224 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have := hpre_13.top_le
    have := hpre_13.heapEnd_le
    have := hpre_2 ▸ hpre_10
    have := env.layout
    have := hpre_13.nextAddr_ge
    simp only [OffStack, inWindow_iff, h24, hsp, show (200#64).toNat = 200 from rfl]
    refine Or.inr ⟨by omega, by omega, by omega, by omega⟩
  · refine mid_ok env p i L hp hL hnC hnK hnF hcp hkf hfail hstop hk hpre_3 hpre_4 hpre_5 hpre_12 hpre_13
      ⟨hpre_6, hpre_7, hpre_8, hpre_9⟩ (hpre_2 ▸ ⟨hpre_10, hpre_11⟩) _ _ ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rv_closeT
    all_goals
      have hsp : (top + 18446744073709551392#64).toNat = top.toNat - 224 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have h8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have h16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have h24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [keep2_1 _ (BitVec.le_def.2 (by omega)) (by
          simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
            toNat_alignToDword, hsp, BitVec.toNat_ofNat]; omega),
        keep1_1 _ (BitVec.le_def.2 (by omega)) (by
          simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
            toNat_alignToDword, hsp, BitVec.toNat_ofNat]; omega)]
      simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]

end Rv64mc.Proof.Transcript.DuplexT

/-- info: 'Rv64mc.Proof.Transcript.DuplexT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.DuplexT.total
