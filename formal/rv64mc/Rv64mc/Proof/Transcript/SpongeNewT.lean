/-
  Rv64mc.Proof.Transcript.SpongeNewT

  `Sponge::new` is total (`specT`): into a slot its caller owns (`Owned`, in a window, 8-byte aligned), from two
  digests in windows apart from the stack below the stack pointer (`OffStack`), it returns with the slot a sponge
  `SpongeT` (`SpongeReprT`): no scalar waiting (`memset` zeroes `n_pending`) and no ground challenge (the tag `0`
  stored). Safety only: the permuted lanes are `keccak_f`'s, whose functional contract is not total
  (`KeccakFSafeT`). `Digest::words`' functional total contract is used through `wordsSafe`, its safety half with
  the digest's bytes read from memory, so no digest is carried as a ghost.

  ## Main definitions

  * `bytesOf`, `WordsPreS`, `PreT`, `PostT`, `specT`

  ## Main results

  * `wordsSafe`, `getMem_zero_of_bytes`, `total`
-/

import Rv64mc.Proof.Transcript.SpongeReprT
import Rv64mc.Proof.Hash.DigestWordsT
import Rv64mc.Proof.Hash.KeccakFT
import Rv64mc.Proof.Runtime.MemsetBytesT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Spec.Transcript.SpongeNew
import Rv64mc.Tactic.SymT
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Sponge.New

namespace Rv64mc.Proof.Transcript.SpongeNewT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Transcript.SpongeReprT
open Rv64mc.Gen.Verifier.Transcript.Sponge.New (Link tmpl)

/-- The `n` bytes from `a` in `m`. -/
def bytesOf (m : MachineState) (a : Word) (n : Nat) : List (BitVec 8) :=
  List.ofFn (n := n) fun k => m.getByte (a + BitVec.ofNat 64 k)

/-- `Digest::words`' total precondition without the digest's value: the slot owned, aligned and in a window, the
    digest apart from it, in a window and apart from the stack below the stack pointer. -/
def WordsPreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Digest.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    ((regs .x10).toNat + Layouts.Digest.byteSize ≤ (regs .x11).toNat ∨
      (regs .x11).toNat + Layouts.Digest.byteSize ≤ (regs .x10).toNat) ∧
    InWin env (regs .x10) Layouts.Digest.byteSize ∧ inWindow (regs .x11) Layouts.Digest.byteSize = true ∧
    OffStack env (regs .x2) (regs .x11) Layouts.Digest.byteSize

/-- **`Digest::words`' safety**: its total contract at the digest its bytes hold. -/
theorem wordsSafe {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : Hash.DigestWordsT.specT env p i need) :
    HoldsT env p i need (WordsPreS env) (fun _ _ _ _ => True) Spec.Hash.DigestWords.Out :=
  fun Q ret top rest regs m ⟨⟨he, hs, hst, hn, ⟨ho, ha, hap, hw, hi, hoff⟩, hal⟩, hW⟩ hstop hk =>
    h (bytesOf m (regs .x11) 32) Q ret top rest regs m
      ⟨⟨he, hs, hst, hn, ⟨⟨⟨by simp [bytesOf], ⟨by
        simp only [bytesOf, List.length_ofFn]; have := (inWindow_iff.1 hi); omega,
        fun k _ => by simp only [bytesOf, List.getElem_ofFn]⟩⟩, ho, ha, hap⟩, hw, hi, hoff⟩, hal⟩, hW⟩ hstop
      fun r' m' ⟨⟨ha', hf, hs', _⟩, hc⟩ => hk r' m' ⟨⟨ha', hf, hs', trivial⟩, hc⟩

/-- Eight zero bytes at an aligned address are a zero doubleword. -/
theorem getMem_zero_of_bytes {m : MachineState} {a : Word} (ha : a.toNat % 8 = 0)
    (h : ∀ k, k < 8 → m.getByte (a + BitVec.ofNat 64 k) = 0#8) : m.getMem a = 0#64 :=
  eq_of_forall_extractByte fun k hk => by
    rw [← getByte_aligned ha hk, h k hk]
    interval_cases k <;> decide

theorem off320 (a : Word) (k : Nat) :
    a + 320#64 + BitVec.ofNat 64 k = a + 224#64 + BitVec.ofNat 64 (96 + k) := by
  rw [BitVec.add_assoc, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The total precondition: the slot owned, in a window and 8-byte aligned; each digest in a window, apart from
    the stack below the stack pointer. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ InWin env (regs .x10) Layouts.Sponge.byteSize ∧
    env.Owned m (regs .x2) (regs .x10) Layouts.Sponge.byteSize ∧
    inWindow (regs .x11) Layouts.Digest.byteSize = true ∧ OffStack env (regs .x2) (regs .x11) Layouts.Digest.byteSize ∧
    inWindow (regs .x12) Layouts.Digest.byteSize = true ∧ OffStack env (regs .x2) (regs .x12) Layouts.Digest.byteSize

/-- The total postcondition: the slot a sponge `SpongeT`. -/
def PostT (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x10)

/-- **The total contract of `Sponge::new`**: `PreT` to `PostT`, writing at most the slot. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (Spec.Whir.SretOut Layouts.Sponge.byteSize)

/-- The state after the permutation (instruction 42): the slot's pointer, the saved registers, the frame of the
    stack stores and the callees, the code, the static data and the saved registers' slots. -/
def TailInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551392#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9

set_option rv_sym.heap true in
/-- From the permutation's return: the state copied into the slot, the tag and the queue zeroed, the return. -/
theorem tail_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS needC : Nat} (hnS : 224 + needS ≤ need) (hnC : 224 + needC ≤ need)
    (hset : Runtime.MemsetBytesT.MemsetSpecT env p L.memset.idx needS)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (Spec.Whir.SretOut Layouts.Sponge.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (ha8 : (regs .x10).toNat % 8 = 0) (hw : InWin env (regs .x10) 328) (ho : env.Owned m top (regs .x10) 328) :
    ∀ R M, TailInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 42, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hlt := hw.lt
  have hne : regs .x10 ≠ env.nextAddr := hw.ne_next (Nat.le_refl _) (by omega)
  rv_introT hinv
  rv_symT hp with [hL, (by omega : env.stackLimit.toNat + 224 ≤ top.toNat), hW.top_le,
    (by decide : (200#64).toNat = 200), (by decide : (104#64).toNat = 104)] using [hcp, hset]
  · have h24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by omega)
    have hsp : (top + 18446744073709551392#64).toNat = top.toNat - 224 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have := hW.top_le
    have := hW.nextAddr_ge
    have := env.layout
    have := ho.1
    unfold InWin at hw
    simp only [OffStack, inWindow_iff, h24, hsp, show (200#64).toNat = 200 from rfl]
    refine Or.inr ⟨by omega, by omega, by omega, by omega⟩
  · have hal : (regs .x10 + 320#64).toNat % 8 = 0 := by rw [toNat_add_ofNat (by omega)]; omega
    rw [getMem_zero_of_bytes hal fun k hk => by
      rw [off320 _ k, hret2_17 (96 + k) (by simp only [BitVec.toNat_ofNat]; omega)]; rfl]
    decide
  · left
    have h224 : (regs .x10 + 224#64).toNat = (regs .x10).toNat + 224 := toNat_add_ofNat (by omega)
    rw [keep2_2 _ (by
        rcases ho.1 with h | h
        · left
          rw [Tactic.next_setMem hne]
          have := hret1_14.1
          have := hinv_14.1
          omega
        · right
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega) (by
        simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
          toNat_alignToDword, h224, BitVec.toNat_ofNat]
        omega), MachineState.getMem_setMem_eq]

/-- A stack slot of the frame is outside a callee's `Out`: the callee's range unfolded to numbers. -/
local macro "not_out" : tactic => `(tactic| (
  simp only [Spec.Hash.KeccakF.Out, Spec.Hash.KeccakF.stateBytes, Spec.Hash.DigestWords.Out, CopyOut, DwordsOf,
    InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, toNat_alignToDword, BitVec.toNat_ofNat,
    Layouts.Digest.byteSize, *]
  omega))

set_option rv_sym.heap true in
/-- **`Sponge::new` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needW needS needK needC : Nat} (hnW : 224 + needW ≤ need) (hnS : 224 + needS ≤ need)
    (hnK : 224 + needK ≤ need) (hnC : 224 + needC ≤ need)
    (hw : Hash.DigestWordsT.specT env p L.words.idx needW)
    (hset : Runtime.MemsetBytesT.MemsetSpecT env p L.memset.idx needS)
    (hkf : Hash.KeccakFT.KeccakFSafeT env p L.keccakF.idx needK)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC) : specT env p i need := by
  rv_autoT hp stop [42] with [hL, (by omega : env.stackLimit.toNat + 224 ≤ top.toNat), hpre_15.top_le,
    (by decide : (200#64).toNat = 200), (by decide : (136#64).toNat = 136), (by decide : (104#64).toNat = 104),
    (by decide : (32#64).toNat = 32)] using [wordsSafe hw, hset, hkf, hcp]
  refine tail_ok env p i L hp hL hnS hnC hset hcp hk hpre_3 hpre_4 hpre_5 hpre_14 hpre_15 hpre_6 hpre_7
    (hpre_2 ▸ ⟨hpre_8, hpre_9⟩) _ _ ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rv_closeT
  all_goals
    clear hpre_7 hpre_8 hpre_11 hpre_13
    have hsp : (top + 18446744073709551392#64).toNat = top.toNat - 224 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h192 : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h160 : (top + 18446744073709551456#64).toNat = top.toNat - 160 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [keep4_1 _ (BitVec.le_def.2 (by omega)) (by not_out), keep3_1 _ (BitVec.le_def.2 (by omega)) (by not_out),
      keep2_1 _ (BitVec.le_def.2 (by omega)) (by not_out), keep1_1 _ (BitVec.le_def.2 (by omega)) (by not_out)]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]

end Rv64mc.Proof.Transcript.SpongeNewT

/-- info: 'Rv64mc.Proof.Transcript.SpongeNewT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.SpongeNewT.total
