/-
  Rv64mc.Proof.Transcript.NextScalarT

  `Transcript::next_scalar` is total (`specT`): from a transcript `TranscriptT` (`TranscriptReprT`) owned with its
  proof (`OwnedT`), and a result's slot in a window apart from both, it returns with the transcript `TranscriptT` and
  owned again, its proof's address kept, writing at most the slot, the sponge and the stream offset, or ends the run
  with `a0 = 2` where `Sponge::absorb` does. Safety only: the partial contract's transcript (`NextScalar.lean`) is
  `absorb`'s functional one, over `duplex`'s permuted lanes.

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `PostK`, `MidInv`, `TailInv`

  ## Main results

  * `tail_ok`, `mid_ok`, `kept`, `out_miss`, `total`
-/

import Rv64mc.Proof.Transcript.NextSafeT
import Rv64mc.Proof.Transcript.AbsorbT
import Rv64mc.Spec.Transcript.NextScalar
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.NextScalar

namespace Rv64mc.Proof.Transcript.NextScalarT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Gen.Verifier.Transcript.Transcript.NextScalar (Link tmpl)

/-- The total precondition: `NextSafeT.PreT`, the same objects, and the slot owned (it is written after calls). -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  NextSafeT.PreT env regs m ∧ env.Owned m (regs .x2) (regs .x10) Layouts.ResultE.byteSize

/-- The total postcondition: `NextSafeT.PostT`. -/
abbrev PostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  NextSafeT.PostT env regs m r' m'

/-- **The total contract of `Transcript::next_scalar`**: `PreT` to `PostT`, writing at most the slot, the sponge
    and the stream offset (`NextScalar.Out`), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (NextScalar.Out Layouts.ResultE.byteSize) (Stop := AbortStop)

/-- What the run gives, from which `PostT` follows with the frame: the sponge `SpongeT`. -/
def PostK (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x11)

/-- The state after `next` (instruction 11): the registers kept, the frame, the code, the static data, the saved
    registers' slots, the sponge `SpongeT` and owned. -/
def TailInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x8 = regs .x10 ∧ R .x19 = regs .x11 ∧
    R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top (NextScalar.Out Layouts.ResultE.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ SpongeT env M (regs .x11) ∧
    env.Owned M top (regs .x11) Layouts.Sponge.byteSize

set_option rv_sym.heap true in
/-- From `next`'s return: on `Ok`, the value absorbed; the result stored; the return. -/
theorem tail_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA : Nat} (hnA : 64 + needA ≤ need) (hab : AbsorbT.specT env p L.absorb.idx needA)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out Layouts.ResultE.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hw : InWin env (regs .x10) 24)
    (ha8 : (regs .x10).toNat % 8 = 0) (hap : Apart (regs .x10) 24 (regs .x11) 360)
    (hos : env.Owned m top (regs .x10) 24) :
    ∀ R M, TailInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 22, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hlt := hw.lt
  have := hW.top_le
  have hown := hos.1
  have o0 : NextScalar.Out Layouts.ResultE.byteSize regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by
    simp only [Layouts.ResultE.byteSize]; omega⟩
  have o8 : NextScalar.Out Layouts.ResultE.byteSize regs m (regs .x10 + 8#64) := Or.inl ⟨by
    rw [toNat_add_ofNat (by omega)]; omega, by
    rw [toNat_add_ofNat (by omega)]; simp only [Layouts.ResultE.byteSize]; omega⟩
  have o16 : NextScalar.Out Layouts.ResultE.byteSize regs m (regs .x10 + 16#64) := Or.inl ⟨by
    rw [toNat_add_ofNat (by omega)]; omega, by
    rw [toNat_add_ofNat (by omega)]; simp only [Layouts.ResultE.byteSize]; omega⟩
  have n0 : regs .x10 ≠ env.nextAddr := hw.ne_next (Nat.le_refl _) (by omega)
  have n8 : regs .x10 + 8#64 ≠ env.nextAddr := hw.ne_next_add (by omega)
  have n16 : regs .x10 + 16#64 ≠ env.nextAddr := hw.ne_next_add (by omega)
  unfold InWin at hw
  unfold Apart at hap
  rv_introT hinv
  rv_symT hp with [hL, (by omega : env.stackLimit.toNat + 64 ≤ top.toNat)] using [hab]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try rv_closeT
    refine Tactic.frame_out (Tactic.frame_out (Tactic.frame_out ?_ o0 n0) o8 n8) o16 n16
    refine Env.Frame.trans hinv_12 hret1_14 (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) fun b hb =>
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    simpa only [Absorb.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] using hb
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hinv_12 o0 n0) o8 n8) o16 n16

/-- The state before `next`'s call (instruction 9): the registers, the frame, the code, the static data, the saved
    registers' slots, the transcript `TranscriptT` and owned. -/
def MidInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x8 = regs .x10 ∧ R .x10 = top + 18446744073709551552#64 ∧
    R .x11 = regs .x11 ∧ R .x19 = regs .x11 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ TranscriptT env M (regs .x11) ∧
    OwnedT env M top (regs .x11)

set_option hygiene false in
/-- A saved register's slot of the frame is kept by `next`, which writes its result's slot and the stream offset. -/
local macro "slot_keep" : tactic => `(tactic| (
  rw [keep1_1 _ (BitVec.le_def.2 (by simp only [hsp, h8, h16, h24, h32, h40]; omega)) (by
    simp only [Next.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, hsp,
      Layouts.ResultE.byteSize, not_or]
    refine ⟨by simp only [h8, h16, h24, h32, h40]; omega, fun h => ?_⟩
    have := congrArg BitVec.toNat h
    simp only [h8, h16, h24, h32, h40, h336] at this
    omega)]))

set_option rv_sym.heap true in
/-- From `next`'s call to its return. -/
theorem mid_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN needA : Nat} (hnN : 64 + needN ≤ need) (hnA : 64 + needA ≤ need)
    (hnx : NextSafeT.specT env p L.next.idx needN) (hab : AbsorbT.specT env p L.absorb.idx needA)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out Layouts.ResultE.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx' : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hw : InWin env (regs .x10) 24)
    (ha8 : (regs .x10).toNat % 8 = 0) (hap : Apart (regs .x10) 24 (regs .x11) 360)
    (hos : env.Owned m top (regs .x10) 24) :
    ∀ R M, MidInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 18, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hT := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hO := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rv_introT hinv
  rv_symT hp stop [22] with [hL, (by omega : env.stackLimit.toNat + 64 ≤ top.toNat)] using [hnx]
  refine tail_ok env p i L hp hL hnA hab hstop hk hstk hnx' hal hW hw ha8 hap hos _ _ ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 11 · rv_closeT
  all_goals
    have hsp : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h40 : (top + 18446744073709551576#64).toNat = top.toNat - 40 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hx := hO.1.1
    have hx2 := hO.1.2
    have := env.layout
    have := hinv_14.2.1
    simp only [Layouts.Transcript.byteSize] at hx hx2
    have h336 : (regs .x11 + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = (regs .x11).toNat + 336 :=
      toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  · refine Env.Frame.trans (Env.Frame.trans (Env.Frame.refl hnx') hinv_14 (Nat.le_refl _) fun _ h => h.elim)
      hret1_14 (by omega) fun b hb => ?_
    simp only [Next.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, hsp,
      Layouts.ResultE.byteSize] at hb
    rcases hb with hb | hb
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb))))
  · rw [hret1_30, hinv_15]
  · exact hret1_15
  · slot_keep; exact hinv_17
  · slot_keep; exact hinv_18
  · slot_keep; exact hinv_19
  · slot_keep; exact hinv_20
  · slot_keep; exact hinv_21
  · exact ⟨hret1_16, hret1_17, hret1_18, hret1_19⟩
  · exact (OwnedT.of_next hO hret1_14.1 hret1_29).sponge

set_option rv_sym.heap true in
/-- **`Transcript::next_scalar` returns `PostK`.** -/
theorem kept (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needN needA : Nat} (hnN : 64 + needN ≤ need) (hnA : 64 + needA ≤ need)
    (hnx : NextSafeT.specT env p L.next.idx needN) (hab : AbsorbT.specT env p L.absorb.idx needA) :
    HoldsT env p i need (PreT env) (PostK env) (NextScalar.Out Layouts.ResultE.byteSize) (Stop := AbortStop) := by
  rv_autoT hp stop [18] with [hL, (by omega : env.stackLimit.toNat + 64 ≤ top.toNat)]
  have hT : TranscriptT env m (regs .x11) :=
    ⟨⟨hpre_6, hpre_7, hpre_8, hpre_9⟩, hpre_10, hpre_11, hpre_12, hpre_13, hpre_14⟩
  have hO : OwnedT env m top (regs .x11) := hpre_2 ▸ ⟨⟨hpre_15, hpre_16⟩, ⟨hpre_17, hpre_18⟩⟩
  refine mid_ok env p i L hp hL hnN hnA hnx hab hstop hk hpre_3 hpre_5 hpre_25 hpre_26 hpre_19 hpre_20 hpre_21
    (hpre_2 ▸ ⟨hpre_23, hpre_24⟩) _ _ ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 21 · rv_closeT
  · refine (hT.frameF hO ?_ hpre_5 (by omega)).1
    rv_closeT
  · refine (hT.frameF hO ?_ hpre_5 (by omega)).2.1
    rv_closeT

/-- `NextScalar.Out` misses the proof's address and the stream's words, the slot apart from the transcript and its
    proof. -/
theorem out_miss {env : Env} {regs : Reg → Word} {m : MachineState} (h : NextSafeT.PreT env regs m) :
    ¬ NextScalar.Out Layouts.ResultE.byteSize regs m (regs .x11 + BitVec.ofNat 64 328) ∧
      ∀ k, (k = 8 ∨ k = 16) →
        ¬ NextScalar.Out Layouts.ResultE.byteSize regs m (m.getMem (regs .x11 + 328#64) + BitVec.ofNat 64 k) := by
  obtain ⟨⟨_, hT, hA, _, hQ, _⟩, _, _, _, hR, hP⟩ := h
  have ha := hT.lt
  have hq := hQ.lt
  simp only [Apart, Layouts.Transcript.byteSize, Layouts.Proof.byteSize, Layouts.ResultE.byteSize] at hA hq hR hP ha ⊢
  have h336 : (regs .x11 + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = (regs .x11).toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  refine ⟨?_, fun k hk => ?_⟩ <;>
    simp only [NextScalar.Out, InRange, Layouts.Sponge.byteSize, not_or] <;>
    refine ⟨?_, ?_, fun he => ?_⟩
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), h336] at this; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), h336] at this; omega

/-- **`Transcript::next_scalar` is total**, from `kept` and `NextScalar.Out`'s frame (`TranscriptT.frameS`). -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needN needA : Nat} (hnN : 64 + needN ≤ need) (hnA : 64 + needA ≤ need)
    (hnx : NextSafeT.specT env p L.next.idx needN) (hab : AbsorbT.specT env p L.absorb.idx needA) :
    specT env p i need :=
  Isa.TContract.mono (kept env p i L hp hL hnN hnA hnx hab) (fun _ _ _ _ h => h)
    (fun _ top regs m _ _ ⟨⟨he, hs, _, hn, hP, _⟩, _⟩ ⟨⟨ha, hf, hst', hK⟩, hc⟩ => by
      have hT := hP.1.1.frameS hK (he.2 ▸ hP.1.2.1) hf hn (by omega) (out_miss hP.1).1 (out_miss hP.1).2
      exact ⟨⟨ha, hf, hst', hT.1, he.2 ▸ hT.2.1, hT.2.2⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Transcript.NextScalarT

/-- info: 'Rv64mc.Proof.Transcript.NextScalarT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.NextScalarT.total
