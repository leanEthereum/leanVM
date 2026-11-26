/-
  Rv64mc.Proof.Transcript.TranscriptNewT

  `Transcript::new` is total (`specT`): into a slot its caller owns, in a window and 8-byte aligned, from a proof
  `ProofT` it owns, apart from the slot, and two digests in windows apart from the stack below the stack pointer, it
  returns with the slot a transcript `TranscriptT` (`TranscriptReprT`) owned with its proof (`OwnedT`), whose proof's
  address is the argument's. Safety only: the sponge's lanes are `Sponge::new`'s permuted ones (`SpongeNewT`), so
  the partial contract's `TranscriptAt` (`New.lean`) is not kept.

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `PostK`, `TailInv`

  ## Main results

  * `tail_ok`, `kept`, `postT_of`, `total`
-/

import Rv64mc.Proof.Transcript.TranscriptReprT
import Rv64mc.Proof.Transcript.SpongeNewT
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Spec.Transcript.New
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.New

namespace Rv64mc.Proof.Transcript.TranscriptNewT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Gen.Verifier.Transcript.Transcript.New (Link tmpl)

/-- The total precondition: the slot owned, in a window and 8-byte aligned; the proof `ProofT`, owned, apart from
    the slot; each digest in a window, apart from the stack below the stack pointer. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ InWin env (regs .x10) Layouts.Transcript.byteSize ∧
    env.Owned m (regs .x2) (regs .x10) Layouts.Transcript.byteSize ∧
    ProofT env m (regs .x11) ∧ env.Owned m (regs .x2) (regs .x11) Layouts.Proof.byteSize ∧
    Apart (regs .x11) Layouts.Proof.byteSize (regs .x10) Layouts.Transcript.byteSize ∧
    inWindow (regs .x12) Layouts.Digest.byteSize = true ∧ OffStack env (regs .x2) (regs .x12) Layouts.Digest.byteSize ∧
    inWindow (regs .x13) Layouts.Digest.byteSize = true ∧ OffStack env (regs .x2) (regs .x13) Layouts.Digest.byteSize

/-- The total postcondition: the slot a transcript `TranscriptT`, owned with its proof, whose proof is the
    argument. -/
def PostT (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  TranscriptT env m' (regs .x10) ∧ OwnedT env m' (regs .x2) (regs .x10) ∧ m'.getMem (regs .x10 + 328#64) = regs .x11

/-- **The total contract of `Transcript::new`**: `PreT` to `PostT`, writing at most the slot. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (Spec.Whir.SretOut Layouts.Transcript.byteSize)

/-- What the run gives, from which `PostT` follows: the sponge `SpongeT`, the proof's address stored, the stream's
    pointer and length kept. -/
def PostK (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x10) ∧ m'.getMem (regs .x10 + 328#64) = regs .x11 ∧
    m'.getMem (regs .x11 + 8#64) = m.getMem (regs .x11 + 8#64) ∧
    m'.getMem (regs .x11 + 16#64) = m.getMem (regs .x11 + 16#64)

/-- The state after `Sponge::new` (instruction 10): the registers kept, the frame, the code, the static data, the
    saved registers' slots, the sponge `SpongeT`, the stream's pointer and length kept. -/
def TailInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551584#64 ∧ R .x8 = regs .x11 ∧ R .x9 = regs .x10 ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top (Spec.Whir.SretOut Layouts.Transcript.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ SpongeT env M (regs .x10) ∧
    M.getMem (regs .x11 + 8#64) = m.getMem (regs .x11 + 8#64) ∧
    M.getMem (regs .x11 + 16#64) = m.getMem (regs .x11 + 16#64)

set_option rv_sym.heap true in
/-- From `Sponge::new`'s return: the proof's address, the offsets and `checked` stored, the return. -/
theorem tail_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) (Spec.Whir.SretOut Layouts.Transcript.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn32 : 32 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (ha8 : (regs .x10).toNat % 8 = 0) (hw : InWin env (regs .x10) 360)
    (ho : env.Owned m top (regs .x10) 360) (hq : (regs .x11).toNat + 48 < 2 ^ 64)
    (hap : Apart (regs .x11) 48 (regs .x10) 360) :
    ∀ R M, TailInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 20, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hlt := hw.lt
  have hown := ho.1
  have := hW.top_le
  have hne : ∀ k, k < 360 → regs .x10 + BitVec.ofNat 64 k ≠ env.nextAddr := fun k hk => hw.ne_next_add hk
  have hin : ∀ k, k < 360 → Spec.Whir.SretOut 360 regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
    ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩
  unfold InWin at hw
  unfold Apart at hap
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 32 ≤ top.toNat)]
  rw [show (regs .x10 + 352#64) = regs .x10 + BitVec.ofNat 64 352 from rfl]
  refine frame_byte_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hinv_14 (hin 328 (by omega))
    (hne 328 (by omega))) (hin 336 (by omega)) (hne 336 (by omega))) (hin 344 (by omega)) (hne 344 (by omega)))
    ?_ ?_ <;> rw [alignToDword_of_aligned ha8 (by decide) (by omega)]
  · exact hin 352 (by omega)
  · exact hne 352 (by omega)

set_option rv_sym.heap true in
/-- **`Transcript::new` returns `PostK`.** -/
theorem kept (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS : Nat} (hnS : 32 + needS ≤ need) (hsn : SpongeNewT.specT env p L.new.idx needS) :
    HoldsT env p i need (PreT env) (PostK env) (Spec.Whir.SretOut Layouts.Transcript.byteSize) := by
  rv_autoT hp stop [20] with [hL, (by omega : env.stackLimit.toNat + 32 ≤ top.toNat)] using [hsn]
  refine tail_ok env p i L hp hk hpre_3 (by omega) hpre_20 hpre_21 hpre_6 hpre_7 (hpre_2 ▸ ⟨hpre_8, hpre_9⟩)
    hpre_14 hpre_15 _ _ ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rv_closeT
  all_goals
    have hsp : (top + 18446744073709551584#64).toNat = top.toNat - 32 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hown := hpre_2 ▸ hpre_8
    have hownq := hpre_2 ▸ hpre_13
    have := env.layout
    simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hown hownq hpre_14 hpre_15 hpre_9
  iterate 3
    · rw [keep1_1 _ (BitVec.le_def.2 (by omega)) (by
        simp only [Spec.Whir.SretOut, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, h8, h16, h24,
          Layouts.Sponge.byteSize]
        omega)]
      simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  all_goals
    have e8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
    have e16 : (regs .x11 + 16#64).toNat = (regs .x11).toNat + 16 := toNat_add_ofNat (by omega)
    rw [keep1_2 _ (by
        rcases hownq with h | h
        · left
          simp (disch := (simp only [h8, h16, h24]; omega)) only [e8, e16, Env.next_setMem_stack]
          omega
        · right; simp only [e8, e16, hsp]; omega) (by
        simp only [Spec.Whir.SretOut, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, e8, e16,
          Layouts.Sponge.byteSize]
        omega)]
    rw [MachineState.getMem_setMem_ne (fun h => by
        have := congrArg BitVec.toNat h; simp only [e8, e16, h24] at this; omega),
      MachineState.getMem_setMem_ne (fun h => by
        have := congrArg BitVec.toNat h; simp only [e8, e16, h16] at this; omega),
      MachineState.getMem_setMem_ne (fun h => by
        have := congrArg BitVec.toNat h; simp only [e8, e16, h8] at this; omega)]

/-- `PostK` gives `PostT`, under `PreT` and `NEXT` not lowered. -/
theorem postT_of {env : Env} {regs r' : Reg → Word} {m m' : MachineState} (hP : PreT env regs m)
    (hK : PostK env regs m r' m') (hn : (env.next m).toNat ≤ (env.next m').toNat) : PostT env regs m r' m' := by
  obtain ⟨_, hw, ⟨ho1, ho2⟩, ⟨hqa, hqw, hs⟩, ⟨hq1, hq2⟩, hap, _⟩ := hP
  obtain ⟨hsp, h328, h8, h16⟩ := hK
  have hq : m'.getMem (regs .x10 + 328#64) = regs .x11 := h328
  refine ⟨⟨hsp, hw, hq ▸ hap, hq ▸ ⟨hqa, hqw, ?_⟩⟩, ⟨⟨by omega, ho2⟩, hq ▸ ⟨by omega, hq2⟩⟩, hq⟩
  unfold NextT.StreamWin at hs ⊢
  rw [h8, h16]
  exact hs

/-- **`Transcript::new` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS : Nat} (hnS : 32 + needS ≤ need) (hsn : SpongeNewT.specT env p L.new.idx needS) :
    specT env p i need :=
  Isa.TContract.mono (kept env p i L hp hL hnS hsn) (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ _ ⟨⟨_, _, _, _, hP, _⟩, _⟩ ⟨⟨ha, hf, hst, hK⟩, hc⟩ => ⟨⟨ha, hf, hst, postT_of hP hK hf.1⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Transcript.TranscriptNewT

/-- info: 'Rv64mc.Proof.Transcript.TranscriptNewT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.TranscriptNewT.total
