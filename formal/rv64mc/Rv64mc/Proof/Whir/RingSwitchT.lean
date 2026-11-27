/-
  Rv64mc.Proof.Whir.RingSwitchT

  `ring_switch(point, s, transcript) -> Result<(E, RingWeight), VerifierError>` is total (`specT`): from a transcript
  `TranscriptAtT` owned with its proof (`OwnedT`), a result's slot of `64` bytes owned, in a window, 8-byte aligned,
  apart from both, the point's header (`a1`) a vector (`VecT`) owned, apart from the slot and the transcript, and `s`
  (`a2`, `a3`) none or in a window and 8-byte aligned, it returns with the transcript `TranscriptAtT` and owned again,
  its proof's address kept, and, unless the slot's word at `16` is the niche `-1` (`Err`), the weight's point and
  coefficients (at `16` and `40`) vectors (`OkW`, what `RingWeight::evaluate`'s `PreT` asks), writing at most the slot,
  the sponge and the stream offset besides what it allocates (`Out`), or the run ends with `a0 = 2` where
  `grind_check`, `samples`, `ring_coefficients` or `ring_target` does. Safety only: the partial contract's value
  (`Spec/Whir/RingSwitch.lean`'s `switchSpec`, `Model.ringSwitchRust`) is owed; `Out` is narrower than its `SwitchOut`.

  Cut at each call, every part keeping `BaseM` (`SavedT.MemOk` with the eight saved registers' slots, the transcript
  `TranscriptAtT` and owned, its proof's address), carried across a call by `base_call` and across a store into the
  frame by `base_slot`: `kept` to `grind_check`'s call (instruction 32), `mid_ok` through it to the branch on its
  result, `err_ok` the error into the slot, `sam_ok` `samples(16)` into the frame, `len_ok` the length check (the
  panic refuted: the length is `16`), `rc_ok` `ring_coefficients` into the frame, `rt_ok` `ring_target`, `fin_ok` the
  point's header copied into the frame, `out_ok` the result into the slot (`stores_ok`) and the return.

  ## Main definitions

  * `PreT`, `Out`, `OkW`, `PostT`, `specT`, `PostK`, `Ctx`, `Mem`, `BaseM`, `SBlk`, `Stores`
  * `ARegs`, `BRegs`, `CRegs`, `RRegs`, `DRegs`, `GRegs`

  ## Main results

  * `base_call`, `base_slot`, `sponge_keep`, `vecT_keep`, `vecT_copy`, `spongeT_setMem`, `stores_ok`, `point_kept`
  * `err_ok`, `sam_ok`, `len_ok`, `rc_ok`, `rt_ok`, `fin_ok`, `out_ok`, `mid_ok`, `kept`, `out_miss`, `total`
-/

import Rv64mc.Proof.Transcript.GrindCheckT
import Rv64mc.Proof.Transcript.SamplesT
import Rv64mc.Proof.Transcript.NextScalarsT
import Rv64mc.Proof.Whir.RingCoefficientsT
import Rv64mc.Proof.Whir.RingTargetT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Spec.Whir.RingSwitch
import Rv64mc.Gen.Tmpl.Verifier.RingSwitch.RingSwitch

namespace Rv64mc.Proof.Whir.RingSwitchT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Transcript
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Gen.Verifier.RingSwitch.RingSwitch (Link tmpl)

/-- The total precondition: the transcript (`a4`) `TranscriptAtT` and owned with its proof; the slot (`a0`, `64`
    bytes) in a window, 8-byte aligned, owned, apart from the transcript and its proof; the point's header (`a1`) a
    vector, owned, apart from the transcript and the slot; `s` (`a3` elements at `a2`) none, or in a window and
    8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAtT env m (regs .x14) ∧ OwnedT env m (regs .x2) (regs .x14) ∧
    InWin env (regs .x10) 64 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 64 ∧
    Apart (regs .x10) 64 (regs .x14) Layouts.Transcript.byteSize ∧
    Apart (regs .x10) 64 (m.getMem (regs .x14 + 328#64)) Layouts.Proof.byteSize ∧
    VecT env m (regs .x11) 16 ∧ env.Owned m (regs .x2) (regs .x11) 24 ∧
    Apart (regs .x11) 24 (regs .x14) Layouts.Transcript.byteSize ∧ Apart (regs .x11) 24 (regs .x10) 64 ∧
    ((regs .x13).toNat = 0 ∨ InWin env (regs .x12) (16 * (regs .x13).toNat) ∧ (regs .x12).toNat % 8 = 0)

/-- What it writes besides its stack and its allocations: the slot, the sponge and the stream offset. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) 64 b ∨ InRange (regs .x14) Layouts.Sponge.byteSize b ∨
    b = regs .x14 + BitVec.ofNat 64 Layouts.Transcript.stream_offset

/-- Unless the slot's word at `16` is the niche `-1` (`Err`), the weight's point and coefficients vectors. -/
def OkW (env : Env) (regs : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (regs .x10 + 16#64) ≠ 18446744073709551615#64 →
    VecT env m' (regs .x10 + 16#64) 16 ∧ VecT env m' (regs .x10 + 40#64) 16

/-- The total postcondition: the transcript `TranscriptAtT` and owned again, its proof's address kept, `OkW`. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  TranscriptAtT env m' (regs .x14) ∧ OwnedT env m' (regs .x2) (regs .x14) ∧
    m'.getMem (regs .x14 + 328#64) = m.getMem (regs .x14 + 328#64) ∧ OkW env regs m'

/-- **The total contract of `ring_switch`**: `PreT` to `PostT`, writing at most the slot, the sponge and the stream
    offset (`Out`), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) Out (Stop := AbortStop)

/-- What the run gives, from which `PostT` follows with the frame: the sponge `SpongeT`, `OkW`. -/
def PostK (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x14) ∧ OkW env regs m'

/-- `PreT`'s facts the parts carry whole. -/
structure Ctx (env : Env) (top : Word) (regs : Reg → Word) (m : MachineState) : Prop where
  tT : TranscriptAtT env m (regs .x14)
  tO : OwnedT env m top (regs .x14)
  wS : InWin env (regs .x10) 64
  aS : (regs .x10).toNat % 8 = 0
  oS : env.Owned m top (regs .x10) 64
  apST : Apart (regs .x10) 64 (regs .x14) Layouts.Transcript.byteSize
  apSP : Apart (regs .x10) 64 (m.getMem (regs .x14 + 328#64)) Layouts.Proof.byteSize
  vP : VecT env m (regs .x11) 16
  oP : env.Owned m top (regs .x11) 24
  apPT : Apart (regs .x11) 24 (regs .x14) Layouts.Transcript.byteSize
  apPS : Apart (regs .x11) 24 (regs .x10) 64
  s : (regs .x13).toNat = 0 ∨ InWin env (regs .x12) (16 * (regs .x13).toNat) ∧ (regs .x12).toNat % 8 = 0

/-- What every part keeps of memory: `SavedT.MemOk` with the eight saved registers' slots, from `top - 8` (the
    return address) down to `top - 64` (`s6`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (Out regs m)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20, regs .x21, regs .x22] m M

/-- The saved slots lie in the `64` bytes below `top`. -/
theorem slots : SlotsIn 64
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64] :=
  slots_le

/-- What the parts keep: `Mem`, the transcript `TranscriptAtT` and owned, its proof's address. -/
def BaseM (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Mem env ret top regs m M ∧ TranscriptAtT env M (regs .x14) ∧ OwnedT env M top (regs .x14) ∧
    M.getMem (regs .x14 + 328#64) = m.getMem (regs .x14 + 328#64)

/-- The registers at `grind_check`'s call (instruction 32): the stack pointer, the arguments in `s0`, `s1`, `s2`,
    `s3`, `s4`, `grind_check`'s `(transcript, 13)`, the callee-saved registers the function does not save. -/
def ARegs (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧ R .x18 = regs .x13 ∧
    R .x19 = regs .x12 ∧ R .x20 = regs .x14 ∧ R .x10 = regs .x14 ∧ R .x11 = 13#64 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The registers kept since the prologue: the stack pointer, the arguments in `s0`, `s1`, `s2`, `s3`, `s4`, the
    callee-saved registers the function does not save. -/
def BRegs (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧ R .x18 = regs .x13 ∧
    R .x19 = regs .x12 ∧ R .x20 = regs .x14 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- **`BaseM` across a call** from `sp` (`top - 144`) writing at most words of the frame below the slots, the
    transcript's sponge and its stream offset, and leaving the sponge `SpongeT`; every other word of the frame read
    as before. -/
theorem base_call {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState} {out' : Word → Prop}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hf : env.Frame (top + 18446744073709551472#64) out' M X) (hc : X.code = M.code) (hs : env.Static X)
    (hout : ∀ a, out' a → (top.toNat - 144 ≤ a.toNat ∧ a.toNat + 64 < top.toNat) ∨
      InRange (regs .x14) Layouts.Sponge.byteSize a ∨ a = regs .x14 + BitVec.ofNat 64 Layouts.Transcript.stream_offset)
    (hk : ∀ a : Word, top + 18446744073709551472#64 ≤ a → ¬ out' a → X.getMem a = M.getMem a)
    (hsT : SpongeT env X (regs .x14)) :
    BaseM env ret top regs m X ∧ ∀ a : Word, top.toNat - 144 ≤ a.toNat → ¬ out' a → X.getMem a = M.getMem a := by
  obtain ⟨hM, hT, hO, hP⟩ := hB
  have hlay := env.layout
  have hnM := hM.1.2.1
  have hsp : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  obtain ⟨_, hwT, hA, _, hQ, _⟩ := id hT
  obtain ⟨⟨hO1, hO2⟩, ⟨hP1, hP2⟩⟩ := id hO
  have ha := hwT.lt
  have hq := hQ.lt
  unfold Apart at hA
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hA hq ha hO1 hO2 hP1 hP2
  have h336 : (regs .x14 + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = (regs .x14).toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  have hno : ∀ a : Word, ((regs .x14).toNat + 360 ≤ a.toNat ∨ a.toNat < (regs .x14).toNat) →
      (a.toNat < env.heapEnd.toNat ∨ top.toNat ≤ a.toNat + 64) → ¬ out' a := fun a h1 h2 h => by
    rcases hout a h with h | h | h
    · omega
    · unfold InRange at h; simp only [Layouts.Sponge.byteSize] at h; omega
    · have := congrArg BitVec.toNat h; rw [h336] at this; omega
  have hms : ¬ out' (regs .x14 + BitVec.ofNat 64 328) ∧
      ∀ k, (k = 8 ∨ k = 16) → ¬ out' (M.getMem (regs .x14 + 328#64) + BitVec.ofNat 64 k) := by
    refine ⟨fun h => ?_, fun k hk => hno _ ?_ ?_⟩
    · rcases hout _ h with h | h | h
      · rw [toNat_add_ofNat (by omega)] at h; omega
      · unfold InRange at h; rw [toNat_add_ofNat (by omega)] at h; simp only [Layouts.Sponge.byteSize] at h; omega
      · have := congrArg BitVec.toNat h; rw [h336, toNat_add_ofNat (by omega)] at this; omega
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
  have hTT := hT.frameS hsT (hO.mono (by rw [hsp]; omega)) hf hnM (by rw [hsp]; omega) hms.1 hms.2
  have rd : ∀ a : Word, top.toNat - 144 ≤ a.toNat → ¬ out' a → X.getMem a = M.getMem a := fun a h1 h2 =>
    hk a (Tactic.le_of_toNat (by omega)) h2
  refine ⟨⟨hM.call slots (by omega) (by omega) hf hc hs (fun a ha => ?_) (fun a h1 h2 => rd a (by omega)
    (hno a (by omega) (by omega))), hTT.1, OwnedT.of_next hO hf.1 hTT.2.2, hTT.2.2.trans hP⟩, rd⟩
  rcases hout a ha with h | h | h
  · exact Tactic.mw_stack ⟨by omega, by omega⟩
  · exact Tactic.mw_out (Or.inr (Or.inl h))
  · exact Tactic.mw_out (Or.inr (Or.inr h))

set_option rv_sym.heap true in
/-- On `grind_check`'s error (instruction 20): the error into the slot, `-1` at its offset `16`, the return. -/
theorem err_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 144 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, BRegs top regs R ∧ R .x12 = 18446744073709551615#64 ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 40, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, h12, hB⟩
  have hM := hB.1
  have hsT := hB.2.1.1
  have hc0 := hM.2.1
  have hn0 := hM.1.1
  rv_introT hR
  rv_introT hM
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_symT hp with [hlim]
  all_goals
    have hlS := hwS.lt
    have hlT := hC.tT.2.1.lt
    have hw24 : InWin env (regs .x10) 24 := hwS.sub (Nat.le_refl _) (by omega)
    have hap24 : Apart (regs .x10) 24 (regs .x14) Layouts.Transcript.byteSize := by
      have := hC.apST; unfold Apart at this ⊢; omega
    have o : ∀ k : Nat, k < 64 → Out regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      Or.inl ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩
    have n : ∀ k : Nat, k < 64 → regs .x10 + BitVec.ofNat 64 k ≠ env.nextAddr := fun k hk => hwS.ne_next_add hk
    have o0 : Out regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by omega⟩
    have n0 : regs .x10 ≠ env.nextAddr := hwS.ne_next (Nat.le_refl _) (by omega)
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hM_1 o0 n0) (o 8 (by omega)) (n 8 (by omega)))
      (o 16 (by omega)) (n 16 (by omega))
  · exact (NextScalarsT.sret_spongeT hw24 hsT hap24 hlT).2.2.1
  · exact (NextScalarsT.sret_spongeT hw24 hsT hap24 hlT).2.2.2
  · exact fun h => absurd h12 h

/-- The samples' block at `P`: allocated (in the input and heap window), at least `16` elements, 8-byte aligned. -/
def SBlk (env : Env) (P : Word) (M : MachineState) : Prop :=
  0x10000000 ≤ P.toNat ∧ P.toNat + 256 ≤ (env.next M).toNat ∧ P.toNat % 8 = 0

set_option rv_sym.heap true in
/-- `samples(16)` into the frame (instruction 48), to the length's load. -/
theorem sam_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 144 + needS ≤ need) (hsa : SamplesT.specT env p L.samples.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hnext : ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M ∧
        M.getMem (top + 18446744073709551496#64) = 16#64 ∧ SBlk env (M.getMem (top + 18446744073709551488#64)) M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 58, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 48, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  rv_introT hR
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_symT hp stop [58] with [hL, hlim] using [hsa]
  all_goals try (obtain ⟨-, ⟨⟨_, _, _, _⟩, _, _, _, _, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩, -⟩ := hB; assumption)
  have hlay := env.layout
  obtain ⟨hB1, -⟩ := base_call hB hlim hret1_14 hret1_27 hret1_15 (fun a ha => by
    simp only [NextScalar.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, InRange,
      Layouts.Vec.byteSize] at ha
    have e : (top + 18446744073709551480#64).toNat = top.toNat - 136 := by tn
    rcases ha with h | h | h
    · rw [e] at h; exact .inl ⟨by omega, by omega⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)) keep1_1 ⟨hret1_23, hret1_24, hret1_25, hret1_26⟩
  obtain ⟨-, -, -, bP, bL⟩ := Runtime.SavedT.hdr_at top 18446744073709551480#64 m1
  obtain ⟨bc, bp, -, -, -⟩ := Runtime.SavedT.hdr_at top 18446744073709551480#64 m1
  simp only [BitVec.reduceAdd] at bP bL bp
  have h16 : m1.getMem (top + 18446744073709551496#64) = 16#64 := bL ▸ hret1_22
  rw [bc, bp] at hret1_19
  have hcl := hret1_21
  simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero] at hcl
  rw [BitVec.add_assoc, show (18446744073709551480#64 : Word) + 16#64 = 18446744073709551496#64 from rfl,
    h16] at hcl
  refine hnext _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hB1, h16, ?_⟩
  obtain ⟨h1, h2, h3⟩ := hret1_19.resolve_left (by simp only [BitVec.toNat_ofNat] at hcl; omega)
  unfold Env.Live at h2
  exact ⟨h1, by simp only [BitVec.toNat_ofNat] at hcl; nlinarith, h3⟩

/-- The registers at `ring_coefficients`' call (instruction 78), the samples at `P`: `BRegs`' but `s4`, which holds
    `P`, `s5` `P + 128`, `s6` `8`, and the arguments `(sp + 0x38, P, P + 128, 8)`. -/
def CRegs (top : Word) (regs : Reg → Word) (P : Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧ R .x18 = regs .x13 ∧
    R .x19 = regs .x12 ∧ R .x20 = P ∧ R .x21 = P + 128#64 ∧ R .x22 = 8#64 ∧
    R .x10 = top + 18446744073709551528#64 ∧ R .x11 = P ∧ R .x12 = P + 128#64 ∧ R .x13 = 8#64 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

set_option rv_sym.heap true in
/-- The samples' length checked against `8` (`panic_fmt` below, refuted: it is `16`), the arguments of
    `ring_coefficients` (instruction 58 to 78). -/
theorem len_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 144 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hnext : ∀ R M, CRegs top regs (M.getMem (top + 18446744073709551488#64)) R ∧ BaseM env ret top regs m M ∧
        SBlk env (M.getMem (top + 18446744073709551488#64)) M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M ∧
        M.getMem (top + 18446744073709551496#64) = 16#64 ∧ SBlk env (M.getMem (top + 18446744073709551488#64)) M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 58, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB, h16, hS⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  rv_introT hR
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_symT hp stop [78] with [hlim]
  · exact absurd hc (by rw [h16]; decide)
  · refine hnext _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩, hB, hS⟩
    all_goals simp only [Tactic.rf]; rw [h16]; rfl

/-- **The sponge kept by a call writing no word of it**, the transcript owned by the caller. -/
theorem sponge_keep {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState} {out' : Word → Prop}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hk : ∀ a : Word, a.toNat < (env.next M).toNat ∨ (top + 18446744073709551472#64).toNat ≤ a.toNat → ¬ out' a →
      X.getMem a = M.getMem a)
    (hout : ∀ a, out' a → top.toNat - 144 ≤ a.toNat ∧ a.toNat + 64 < top.toNat) : SpongeT env X (regs .x14) := by
  obtain ⟨hM, hT, hO, -⟩ := hB
  have hlay := env.layout
  have hnM := hM.1.2.1
  have hsp : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  have hlT := hT.2.1.lt
  have hO1 := hO.1.1
  simp only [Layouts.Transcript.byteSize] at hO1 hlT
  have e320 : (regs .x14 + 320#64).toNat = (regs .x14).toNat + 320 := toNat_add_ofNat (k := 320) (by omega)
  refine spongeT_of_get hT.1 (hk _ (by omega) fun h => ?_) (hk _ (by omega) fun h => ?_)
  · have := hout _ h; omega
  · have := hout _ h; omega

/-- **A vector's header kept** by a memory agreeing on its three words, `NEXT` not lowered. -/
theorem vecT_keep {env : Env} {M X : MachineState} {a : Word} (h : VecT env M a 16)
    (h0 : X.getMem a = M.getMem a) (h8 : X.getMem (a + 8#64) = M.getMem (a + 8#64))
    (h16 : X.getMem (a + 16#64) = M.getMem (a + 16#64)) (hn : (env.next M).toNat ≤ (env.next X).toNat) :
    VecT env X a 16 := by
  have e0 : rvCapAt a = a := by simp only [rvCapAt, Layouts.RawVecInner.cap]; exact BitVec.add_zero _
  have e8 : rvPtrAt a = a + 8#64 := by simp only [rvPtrAt, Layouts.RawVecInner.ptr]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2.keep (by rw [e0]; exact h0) (by rw [e8]; exact h8) hn, ?_⟩
  simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero] at h3 ⊢
  rw [show a + BitVec.ofNat 64 16 = a + 16#64 from rfl, h16, h0]
  exact h3

/-- The registers at `ring_target`'s return (instruction 96): the stack pointer, `s0` (the slot), `s1` (the
    point's header), the callee-saved registers the function does not save. -/
def DRegs (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The registers at `ring_coefficients`' return (instruction 82): `CRegs`' saved ones. -/
def RRegs (top : Word) (regs : Reg → Word) (P : Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧ R .x18 = regs .x13 ∧
    R .x19 = regs .x12 ∧ R .x20 = P ∧ R .x21 = P + 128#64 ∧ R .x22 = 8#64 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- **A vector's header copied** from `a` in `M` to `b` in `X` (in a window, 8-byte aligned), `NEXT` not lowered. -/
theorem vecT_copy {env : Env} {M X : MachineState} {a b : Word} (h : VecT env M a 16) (hw : InWin env b 24)
    (hab : b.toNat % 8 = 0) (h0 : X.getMem b = M.getMem a) (h8 : X.getMem (b + 8#64) = M.getMem (a + 8#64))
    (h16 : X.getMem (b + 16#64) = M.getMem (a + 16#64)) (hn : (env.next M).toNat ≤ (env.next X).toNat) :
    VecT env X b 16 := by
  have c0 : ∀ x : Word, rvCapAt x = x := fun x => by
    simp only [rvCapAt, Layouts.RawVecInner.cap]; exact BitVec.add_zero _
  have c8 : ∀ x : Word, rvPtrAt x = x + 8#64 := fun x => by simp only [rvPtrAt, Layouts.RawVecInner.ptr]
  obtain ⟨-, ⟨-, -, h3, h4⟩, h5⟩ := h
  rw [c0, c8] at h3
  rw [c0] at h4
  simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero] at h5 ⊢
  refine ⟨hw, ⟨hw.sub (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega), hab, ?_, ?_⟩, ?_⟩
  · rw [c0, c8, h0, h8]; exact h3.mono hn
  · rw [c0, h0]; exact h4
  · simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero]
    rw [show b + BitVec.ofNat 64 16 = b + 16#64 from rfl, h16, h0]; exact h5

/-- A store missing the sponge's two words keeps it. -/
theorem spongeT_setMem {env : Env} {M : MachineState} {T b v : Word} (hT : SpongeT env M T)
    (hb : b.toNat + 8 ≤ T.toNat ∨ T.toNat + 328 ≤ b.toNat) (hlT : T.toNat + 328 < 2 ^ 64) :
    SpongeT env (M.setMem b v) T := by
  have e : (T + 320#64).toNat = T.toNat + 320 := toNat_add_ofNat (k := 320) (by omega)
  exact spongeT_of_get hT (MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)))
    (MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)))

/-- The result's eight words stored into the slot at `a`. -/
abbrev Stores (M : MachineState) (a v0 v1 v2 v3 v4 v5 v6 v7 : Word) : MachineState :=
  (((((((M.setMem a v0).setMem (a + 8#64) v1).setMem (a + 16#64) v2).setMem (a + 24#64) v3).setMem (a + 32#64)
    v4).setMem (a + 40#64) v5).setMem (a + 48#64) v6).setMem (a + 56#64) v7

/-- **The slot's stores**, apart from the transcript, keep its sponge; they keep `NEXT`; the two headers read back. -/
theorem stores_ok {env : Env} {M : MachineState} {a T v0 v1 v2 v3 v4 v5 v6 v7 : Word} (hw : InWin env a 64) :
    (SpongeT env M T → Apart a 64 T Layouts.Transcript.byteSize → T.toNat + 360 < 2 ^ 64 →
      SpongeT env (Stores M a v0 v1 v2 v3 v4 v5 v6 v7) T) ∧
    env.next (Stores M a v0 v1 v2 v3 v4 v5 v6 v7) = env.next M ∧
    (Stores M a v0 v1 v2 v3 v4 v5 v6 v7).getMem (a + 16#64) = v2 ∧
    (Stores M a v0 v1 v2 v3 v4 v5 v6 v7).getMem (a + 16#64 + 8#64) = v3 ∧
    (Stores M a v0 v1 v2 v3 v4 v5 v6 v7).getMem (a + 16#64 + 16#64) = v4 ∧
    (Stores M a v0 v1 v2 v3 v4 v5 v6 v7).getMem (a + 40#64) = v5 ∧
    (Stores M a v0 v1 v2 v3 v4 v5 v6 v7).getMem (a + 40#64 + 8#64) = v6 ∧
    (Stores M a v0 v1 v2 v3 v4 v5 v6 v7).getMem (a + 40#64 + 16#64) = v7 := by
  have hlt := hw.lt
  have e : ∀ k : Nat, k < 64 → (a + BitVec.ofNat 64 k).toNat = a.toNat + k := fun k hk => toNat_add_ofNat (by omega)
  have ne : ∀ j k : Nat, j < 64 → k < 64 → j ≠ k → a + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 k :=
    fun j k hj hk h => Tactic.ne_of_toNat (by rw [e j hj, e k hk]; omega)
  have z : a = a + BitVec.ofNat 64 0 := (BitVec.add_zero a).symm
  have a1 : a + 16#64 + 8#64 = a + 24#64 := by rw [BitVec.add_assoc]; rfl
  have a2 : a + 16#64 + 16#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl
  have a3 : a + 40#64 + 8#64 = a + 48#64 := by rw [BitVec.add_assoc]; rfl
  have a4 : a + 40#64 + 16#64 = a + 56#64 := by rw [BitVec.add_assoc]; rfl
  refine ⟨fun hT hap hlT => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Apart at hap
    simp only [Layouts.Transcript.byteSize] at hap
    have s : ∀ k : Nat, k ≤ 56 → (a + BitVec.ofNat 64 k).toNat + 8 ≤ T.toNat ∨ T.toNat + 328 ≤
        (a + BitVec.ofNat 64 k).toNat := fun k hk => by rw [e k (by omega)]; omega
    refine spongeT_setMem (spongeT_setMem (spongeT_setMem (spongeT_setMem (spongeT_setMem (spongeT_setMem
      (spongeT_setMem (spongeT_setMem hT ?_ (by omega)) (s 8 (by omega)) (by omega)) (s 16 (by omega)) (by omega))
      (s 24 (by omega)) (by omega)) (s 32 (by omega)) (by omega)) (s 40 (by omega)) (by omega)) (s 48 (by omega))
      (by omega)) (s 56 (by omega)) (by omega)
    omega
  · have n : ∀ k : Nat, k < 64 → a + BitVec.ofNat 64 k ≠ env.nextAddr := fun k hk => hw.ne_next_add hk
    rw [Tactic.next_setMem (n 56 (by omega)), Tactic.next_setMem (n 48 (by omega)),
      Tactic.next_setMem (n 40 (by omega)), Tactic.next_setMem (n 32 (by omega)),
      Tactic.next_setMem (n 24 (by omega)), Tactic.next_setMem (n 16 (by omega)),
      Tactic.next_setMem (n 8 (by omega)), Tactic.next_setMem (hw.ne_next (Nat.le_refl _) (by omega))]
  all_goals simp only [Stores, a1, a2, a3, a4]
  all_goals
    repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)
      (by omega) (by omega))])

/-- **The point's header kept** since the entry: it is the caller's, apart from the slot and the transcript. -/
theorem point_kept {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState}
    (hC : Ctx env top regs m) (hB : BaseM env ret top regs m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (k : Nat) (hk : k ≤ 16) :
    M.getMem (regs .x11 + BitVec.ofNat 64 k) = m.getMem (regs .x11 + BitVec.ofNat 64 k) := by
  have ho := hC.oP
  have hlP := ho.2
  have hS := hC.apPS
  have hT := hC.apPT
  have hlT := hC.tT.2.1.lt
  unfold Apart at hS hT
  simp only [Layouts.Transcript.byteSize] at hT hlT
  have h336 : (regs .x14 + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = (regs .x14).toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  have e : (regs .x11 + BitVec.ofNat 64 k).toNat = (regs .x11).toNat + k := toNat_add_ofNat (by omega)
  refine getMem_owned_out hB.1.1 hnx hlim ho (by omega) fun h => ?_
  rcases h with h | h | h
  · unfold InRange at h; rw [e] at h; omega
  · unfold InRange at h; rw [e] at h; simp only [Layouts.Sponge.byteSize] at h; omega
  · have := congrArg BitVec.toNat h; rw [e, h336] at this; omega

/-- **`BaseM` across a store into the frame** below the slots. -/
theorem base_slot {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hlo : top.toNat - 144 ≤ a.toNat) (hhi : a.toNat + 72 ≤ top.toNat) : BaseM env ret top regs m (M.setMem a v) := by
  obtain ⟨hM, hT, hO, hP⟩ := hB
  have hlay := env.layout
  obtain ⟨h1, n1⟩ := hM.slot (v := v) slots (F := 144) hlim hlo (by omega)
  have hnM := hM.1.2.1
  have hlT := hT.2.1.lt
  have hq := hT.2.2.2.2.1.lt
  obtain ⟨⟨hO1, -⟩, ⟨hP1, -⟩⟩ := id hO
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hlT hq hO1 hP1
  have rd : ∀ x : Word, (x.toNat + 8 ≤ top.toNat - 144 ∨ top.toNat ≤ x.toNat) → (M.setMem a v).getMem x = M.getMem x :=
    fun x hx => MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))
  have e : ∀ (b : Word) (k : Nat), b.toNat + k < 2 ^ 64 → (b + BitVec.ofNat 64 k).toNat = b.toNat + k :=
    fun b k h => toNat_add_ofNat h
  have r328 : (M.setMem a v).getMem (regs .x14 + 328#64) = M.getMem (regs .x14 + 328#64) :=
    rd _ (by rw [e _ 328 (by omega)]; omega)
  refine ⟨h1, hT.of_get (rd _ (by omega)) (rd _ (by rw [e _ 320 (by omega)]; omega)) r328
    (rd _ (by rw [e _ 8 (by omega)]; omega)) (rd _ (by rw [e _ 16 (by omega)]; omega)),
    OwnedT.of_next hO (by rw [n1]) r328, r328.trans hP⟩

/-- The registers at the stores into the slot (instruction 114): `DRegs`, the point's header (`a2`..`a4`) as at the
    entry, the coefficients' (`a5`..`a7`) as in the frame. -/
def GRegs (top : Word) (regs : Reg → Word) (m X : MachineState) (R : Reg → Word) : Prop :=
  DRegs top regs R ∧ R .x12 = m.getMem (regs .x11) ∧ R .x13 = m.getMem (regs .x11 + 8#64) ∧
    R .x14 = m.getMem (regs .x11 + 16#64) ∧ R .x15 = X.getMem (top + 18446744073709551528#64) ∧
    R .x16 = X.getMem (top + 18446744073709551536#64) ∧ R .x17 = X.getMem (top + 18446744073709551544#64)

set_option rv_sym.heap true in
/-- The target and the two headers into the slot, the return (instruction 114). -/
theorem out_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 144 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, GRegs top regs m M R ∧ BaseM env ret top regs m M ∧ VecT env M (top + 18446744073709551528#64) 16 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB, hV⟩
  have hM := hB.1
  rv_introT hR
  rv_introT hM
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  have hX := PLift.up (And.intro hC (And.intro hB hV))
  clear hC hB hV
  rv_symT hp with [hlim]
  all_goals
    obtain ⟨hC, hB, hV⟩ := hX.down
    have hlS := hwS.lt
    have hlT := hC.tT.2.1.lt
    have e : ∀ k : Nat, k < 64 → (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k := fun k hk =>
      toNat_add_ofNat (by omega)
    have o : ∀ k : Nat, k < 64 → Out regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      Or.inl ⟨by rw [e k hk]; omega, by rw [e k hk]; omega⟩
    have n : ∀ k : Nat, k < 64 → regs .x10 + BitVec.ofNat 64 k ≠ env.nextAddr := fun k hk => hwS.ne_next_add hk
    have o0 : Out regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by omega⟩
    have n0 : regs .x10 ≠ env.nextAddr := hwS.ne_next (Nat.le_refl _) (by omega)
    have hso := stores_ok (M := M) (T := regs .x14) (v0 := R .x10) (v1 := R .x11) (v2 := m.getMem (regs .x11))
      (v3 := m.getMem (regs .x11 + 8#64)) (v4 := m.getMem (regs .x11 + 16#64))
      (v5 := M.getMem (top + 18446744073709551528#64)) (v6 := M.getMem (top + 18446744073709551536#64))
      (v7 := M.getMem (top + 18446744073709551544#64)) hwS
    have hsT := hso.1 hB.2.1.1 hC.apST hlT
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out
      (Tactic.frame_out (Tactic.frame_out hM_1 o0 n0) (o 8 (by omega)) (n 8 (by omega))) (o 16 (by omega))
      (n 16 (by omega))) (o 24 (by omega)) (n 24 (by omega))) (o 32 (by omega)) (n 32 (by omega)))
      (o 40 (by omega)) (n 40 (by omega))) (o 48 (by omega)) (n 48 (by omega))) (o 56 (by omega)) (n 56 (by omega))
  · exact hsT.1
  · exact hsT.2.1
  · exact hsT.2.2.1
  · exact hsT.2.2.2
  · intro _
    have hnS := hso.2.1
    refine ⟨vecT_copy hC.vP (hwS.sub (by have := e 16 (by omega); omega) (by have := e 16 (by omega); omega))
      (by have := e 16 (by omega); omega) hso.2.2.1 hso.2.2.2.1 hso.2.2.2.2.1 (by rw [hnS]; exact hM_1.1),
      vecT_copy hV (hwS.sub (by have := e 40 (by omega); omega) (by have := e 40 (by omega); omega))
      (by have := e 40 (by omega); omega) hso.2.2.2.2.2.1 ?_ ?_ (by rw [hnS])⟩
    · rw [hso.2.2.2.2.2.2.1]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    · rw [hso.2.2.2.2.2.2.2]; simp only [BitVec.add_assoc, BitVec.reduceAdd]

set_option rv_sym.heap true in
/-- The point's header copied into the frame (`sp + 0x20`), the target, the point's and the coefficients' headers
    into the slot, the return (instruction 96). -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 144 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hC : Ctx env top regs m)
    (hnext : ∀ R M, GRegs top regs m M R ∧ BaseM env ret top regs m M ∧
        VecT env M (top + 18446744073709551528#64) 16 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, DRegs top regs R ∧ BaseM env ret top regs m M ∧ VecT env M (top + 18446744073709551528#64) 16 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 96, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB, hV⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  rv_introT hR
  have hwP : InWin env (regs .x11) 24 := hC.vP.1
  have haP := hC.vP.2.1.2.1
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  have hX := PLift.up (And.intro hC (And.intro hB hV))
  clear hC hB hV
  rv_symT hp stop [114] with [hlim]
  obtain ⟨hC, hB, hV⟩ := hX.down
  have hnM := hB.1.1.2.1
  have pk := point_kept hC hB (by omega) (by omega)
  refine hnext _ _ ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  iterate 8 · rfl
  all_goals try simp only [Tactic.rf]
  · simpa using pk 0 (by omega)
  · exact pk 8 (by omega)
  · exact pk 16 (by omega)
  iterate 3 simp (disch := decide) only [getMem_setMem_off]
  · refine base_slot (base_slot (base_slot hB hlim ?_ ?_) hlim ?_ ?_) hlim ?_ ?_ <;> tn
  · have hlay := env.layout
    have n : ∀ c : Word, 2 ^ 64 - 144 ≤ c.toNat → top + c ≠ env.nextAddr := fun c hc =>
      Tactic.ne_of_toNat (by rw [BitVec.toNat_add]; omega)
    refine vecT_keep hV (by simp (disch := decide) only [getMem_setMem_off]) ?_ ?_ ?_
    · rw [BitVec.add_assoc]; simp (disch := decide) only [BitVec.reduceAdd, getMem_setMem_off]
    · rw [BitVec.add_assoc]; simp (disch := decide) only [BitVec.reduceAdd, getMem_setMem_off]
    · rw [Tactic.next_setMem (n _ (by decide)), Tactic.next_setMem (n _ (by decide)),
        Tactic.next_setMem (n _ (by decide))]

set_option rv_sym.heap true in
/-- `ring_target(s, f, g)` (instruction 82 to 96), `f` and `g` the samples' first eight and last eight. -/
theorem rt_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needT : Nat} (hnT : 144 + needT ≤ need)
    (hrt : RingTargetT.specT env p L.ringTarget.idx needT)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hC : Ctx env top regs m)
    (hnext : ∀ R M, DRegs top regs R ∧ BaseM env ret top regs m M ∧ VecT env M (top + 18446744073709551528#64) 16 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 96, ret, top⟩ :: rest, R, M⟩) :
    ∀ P R M, RRegs top regs P R ∧ BaseM env ret top regs m M ∧ SBlk env P M ∧
        VecT env M (top + 18446744073709551528#64) 16 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 82, ret, top⟩ :: rest, R, M⟩ := by
  intro P R M ⟨hR, hB, hS, hV⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  have hnM := hB.1.1.2.1
  obtain ⟨hP1, hP2, hP3⟩ := hS
  rv_introT hR
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  have hs := hC.s
  have hX := PLift.up (And.intro hC (And.intro hB hV))
  clear hC hB hV
  rv_symT hp stop [96] with [hL, hlim] using [hrt]
  obtain ⟨hC, hB, hV⟩ := hX.down
  obtain ⟨hB1, rd1⟩ := base_call hB hlim hret1_14 hret1_16 hret1_15 (fun _ h => h.elim)
    (fun a h _ => keep1_1 a h) (sponge_keep (out' := fun _ => False) hB hlim (fun a h _ => keep1_2 a h)
      fun _ h => h.elim)
  have r : ∀ k : Nat, k ≤ 16 → m1.getMem (top + 18446744073709551528#64 + BitVec.ofNat 64 k) =
      M.getMem (top + 18446744073709551528#64 + BitVec.ofNat 64 k) := fun k hk =>
    rd1 _ (by rw [BitVec.add_assoc, BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega) id
  refine hnext _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hB1, vecT_keep hV ?_ (r 8 (by omega)) (r 16 (by omega))
    hret1_14.1⟩
  simpa using r 0 (by omega)

set_option rv_sym.heap true in
/-- `ring_coefficients` into the frame (`sp + 0x38`), `f` and `g` the samples' first eight and last eight
    (instruction 78 to 82). -/
theorem rc_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hnC : 144 + needC ≤ need)
    (hrc : RingCoefficientsT.specT env p L.ringCoefficients.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hnext : ∀ P R M, RRegs top regs P R ∧ BaseM env ret top regs m M ∧ SBlk env P M ∧
        VecT env M (top + 18446744073709551528#64) 16 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 82, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, CRegs top regs (M.getMem (top + 18446744073709551488#64)) R ∧ BaseM env ret top regs m M ∧
        SBlk env (M.getMem (top + 18446744073709551488#64)) M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB, hS⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  have hnM := hB.1.1.2.1
  obtain ⟨hP1, hP2, hP3⟩ := hS
  generalize M.getMem (top + 18446744073709551488#64) = P at hR hP1 hP2 hP3
  rv_introT hR
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_symT hp stop [82] with [hL, hlim] using [hrc]
  have hV1 : VecT env m1 (top + 18446744073709551528#64) 16 :=
    ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩
  have e88 : (top + 18446744073709551528#64).toNat = top.toNat - 88 := by tn
  obtain ⟨hB1, rd1⟩ := base_call hB hlim hret1_14 hret1_24 hret1_15 (fun a ha => .inl (by
      simp only [Spec.Whir.SretOut, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, e88,
        Layouts.Vec.byteSize] at ha
      omega)) keep1_1 (sponge_keep hB hlim keep1_2 fun a ha => by
      simp only [Spec.Whir.SretOut, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, e88,
        Layouts.Vec.byteSize] at ha
      omega)
  exact hnext P _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hB1,
    ⟨hP1, by have := hret1_14.1; omega, hP3⟩, hV1⟩

set_option rv_sym.heap true in
/-- `grind_check(13)` (instruction 32), then the branch on its result: the error (instruction 40) or `samples`'
    call (48). -/
theorem mid_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG : Nat} (hnG : 144 + needG ≤ need)
    (hgc : GrindCheckT.specT env p L.grindCheck.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hC : Ctx env top regs m)
    (herr : ∀ R M, BRegs top regs R ∧ R .x12 = 18446744073709551615#64 ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 40, ret, top⟩ :: rest, R, M⟩)
    (hok : ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 48, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, ARegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 32, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hinv, hBM⟩
  have hc0 := hBM.1.2.1
  have hn0 := hBM.1.1.1
  have hs0 := hBM.1.2.2.1
  rv_introT hinv
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_symT hp stop [36] with [hL, hlim] using [hgc]
  -- `grind_check`'s precondition
  all_goals try (obtain ⟨-, ⟨⟨_, _, _, _⟩, _, _, _, _, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩, -⟩ := hBM; assumption)
  have hT1 : TranscriptAtT env m1 (regs .x14) :=
    ⟨⟨hret1_16, hret1_17, hret1_18, hret1_19⟩, hret1_20, hret1_21, hret1_22, hret1_23, hret1_24⟩
  obtain ⟨hB1, rd1⟩ := base_call hBM hlim hret1_14 hret1_30 hret1_15 (fun a ha => by
    simp only [GrindCheck.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] at ha
    exact Or.inr ha) keep1_1 hT1.1
  have hc1 := hret1_30.trans hc0
  have hn1 := hret1_14.1
  have hs1 := hret1_15
  clear hret1_14 hret1_16 hret1_17 hret1_18 hret1_19 hret1_20 hret1_21 hret1_22 hret1_23 hret1_24 hret1_25 hret1_26
    hret1_27 hret1_28 hret1_29 keep1_1 keep1_2 hT1 hBM
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  rv_symT hp stop [40, 48] with [hL, hlim]
  · exact hok _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hB1⟩
  · exact herr _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, hB1⟩

set_option rv_sym.heap true in
/-- **`ring_switch` returns `PostK`**: the prologue, then the parts. -/
theorem kept (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needG needS needC needT : Nat} (hnG : 144 + needG ≤ need) (hnS : 144 + needS ≤ need)
    (hnC : 144 + needC ≤ need) (hnT : 144 + needT ≤ need) (hgc : GrindCheckT.specT env p L.grindCheck.idx needG)
    (hsa : SamplesT.specT env p L.samples.idx needS)
    (hrc : RingCoefficientsT.specT env p L.ringCoefficients.idx needC)
    (hrt : RingTargetT.specT env p L.ringTarget.idx needT) :
    HoldsT env p i need (PreT env) (PostK env) Out (Stop := AbortStop) := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)]
  have hC : Ctx env top regs m := hpre_2 ▸ ⟨⟨⟨hpre_6, hpre_7, hpre_8, hpre_9⟩, hpre_10, hpre_11, hpre_12, hpre_13,
    hpre_14⟩, ⟨⟨hpre_15, hpre_16⟩, ⟨hpre_17, hpre_18⟩⟩, hpre_19, hpre_20, ⟨hpre_21, hpre_22⟩, hpre_23, hpre_24,
    ⟨hpre_25, ⟨hpre_26, hpre_27, hpre_28, hpre_29⟩, hpre_30⟩, ⟨hpre_31, hpre_32⟩, hpre_33, hpre_34, hpre_35⟩
  clear hpre_6 hpre_7 hpre_8 hpre_9 hpre_10 hpre_11 hpre_12 hpre_13 hpre_14 hpre_15 hpre_16 hpre_17 hpre_18 hpre_19
    hpre_20 hpre_21 hpre_22 hpre_23 hpre_24 hpre_25 hpre_26 hpre_27 hpre_28 hpre_29 hpre_30 hpre_31 hpre_32 hpre_33
    hpre_34 hpre_35
  have hn : 144 ≤ need := by omega
  have hrest := sam_ok env p i L hp hL hnS hsa hstop hpre_3 hpre_36 hpre_37
    (len_ok env p i L hp hpre_3 hn hpre_36 hpre_37
      (rc_ok env p i L hp hL hnC hrc hstop hpre_3 hpre_36 hpre_37
        (rt_ok env p i L hp hL hnT hrt hstop hpre_3 hpre_36 hpre_37 hC
          (fin_ok env p i L hp hpre_3 hn hpre_36 hpre_37 hC (out_ok env p i L hp hk hpre_3 hn hpre_36 hpre_37 hC)))))
  have herr := err_ok env p i L hp hk hpre_3 hn hpre_36 hpre_37 hC
  rv_symT hp stop [32] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)]
  refine mid_ok env p i L hp hL hnG hgc hstop hpre_3 hpre_36 hpre_37 hC herr hrest _ _
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  iterate 16 · rv_closeT
  · simp only [Runtime.SavedT.Saved]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq, and_true]
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).1
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.1
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.2

/-- `Out` misses the proof's address and the stream's words, the slot apart from the transcript and its proof. -/
theorem out_miss {env : Env} {regs : Reg → Word} {m : MachineState} (h : PreT env regs m) :
    ¬ Out regs m (regs .x14 + BitVec.ofNat 64 328) ∧
      ∀ k, (k = 8 ∨ k = 16) → ¬ Out regs m (m.getMem (regs .x14 + 328#64) + BitVec.ofNat 64 k) := by
  obtain ⟨⟨_, hT, hA, _, hQ, _⟩, _, hW, _, _, hR, hP, -⟩ := h
  have ha := hT.lt
  have hq := hQ.lt
  have hw := hW.lt
  unfold Apart at hA hR hP
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at *
  have h336 : (regs .x14 + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = (regs .x14).toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  refine ⟨?_, fun k hk => ?_⟩ <;>
    simp only [Out, InRange, Layouts.Sponge.byteSize, not_or] <;>
    refine ⟨?_, ?_, fun he => ?_⟩
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), h336] at this; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), h336] at this; omega

/-- **`ring_switch` is total**, from `kept` and `Out`'s frame (`TranscriptAtT.frameS`). -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needG needS needC needT : Nat} (hnG : 144 + needG ≤ need) (hnS : 144 + needS ≤ need)
    (hnC : 144 + needC ≤ need) (hnT : 144 + needT ≤ need) (hgc : GrindCheckT.specT env p L.grindCheck.idx needG)
    (hsa : SamplesT.specT env p L.samples.idx needS)
    (hrc : RingCoefficientsT.specT env p L.ringCoefficients.idx needC)
    (hrt : RingTargetT.specT env p L.ringTarget.idx needT) :
    specT env p i need :=
  Isa.TContract.mono (kept env p i L hp hL hnG hnS hnC hnT hgc hsa hrc hrt) (fun _ _ _ _ h => h)
    (fun _ top regs m _ _ ⟨⟨he, hs, _, hn, hP, _⟩, _⟩ ⟨⟨ha, hf, hst', hK, hV⟩, hc⟩ => by
      have hT := hP.1.frameS hK (he.2 ▸ hP.2.1) hf hn (by omega) (out_miss hP).1 (out_miss hP).2
      exact ⟨⟨ha, hf, hst', hT.1, he.2 ▸ hT.2.1, hT.2.2, hV⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Whir.RingSwitchT

/-- info: 'Rv64mc.Proof.Whir.RingSwitchT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.RingSwitchT.total
