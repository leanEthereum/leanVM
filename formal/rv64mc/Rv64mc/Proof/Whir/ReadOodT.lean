/-
  Rv64mc.Proof.Whir.ReadOodT

  `read_ood(transcript, vars)` (`lib.rs`: the proof of work checked, `vars` challenges sampled, a scalar read) is
  total (`specT`): from a transcript `TranscriptAtT` (`TranscriptReprT`) owned with its proof (`OwnedT`), and a
  result's slot of `40` bytes owned, in a window, 8-byte aligned, apart from both, it returns with the transcript
  `TranscriptAtT` and owned again, its proof's address kept, and, unless the slot holds `Err` (its first word the
  niche `-1`), the point at the slot's head a vector (`VecReprT.VecT`), writing at most the slot, the sponge and the
  stream offset besides what it allocates, or ends the run with `a0 = 2` where `grind_check`, `samples` or
  `next_scalar` does. Safety only: the partial contract's point and value (`Spec/Whir/Transcript.lean`'s
  `readOodSpec`) are its callees' functional ones.

  Cut at `grind_check`'s call (`kept`, `AInv`), from there through `grind_check` and `samples` (`mid_ok`) to
  `next_scalar`'s call (`CInv`), and from there to the return (`tail_ok`). The memory facts the parts keep
  (`BaseM`) are carried across each call by its frame (`TranscriptAtT.frameS`, `frame`), not by the executor.

  ## Main definitions

  * `PreT`, `OkVec`, `PostT`, `specT`, `PostK`, `Ctx`, `BaseM`, `AInv`, `CInv`

  ## Main results

  * `vecT_keep2`, `tail_ok`, `mid_ok`, `kept`, `out_miss`, `total`
-/

import Rv64mc.Proof.Transcript.NextScalarsT
import Rv64mc.Proof.Transcript.GrindCheckT
import Rv64mc.Proof.Transcript.SamplesT
import Rv64mc.Spec.Whir.Transcript
import Rv64mc.Gen.Tmpl.Verifier.ReadOod

namespace Rv64mc.Proof.Whir.ReadOodT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Transcript
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Proof.Transcript.NextScalarsT (sret_spongeT vecT_stores)
open Rv64mc.Gen.Verifier.ReadOod (Link tmpl)

/-- The total precondition: the transcript at `a1` `TranscriptAtT` and owned with its proof, the result's slot (`40`
    bytes) owned, in a window, 8-byte aligned, apart from both. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAtT env m (regs .x11) ∧ OwnedT env m (regs .x2) (regs .x11) ∧
    InWin env (regs .x10) Layouts.ResultVecEE.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    env.Owned m (regs .x2) (regs .x10) Layouts.ResultVecEE.byteSize ∧
    Apart (regs .x10) Layouts.ResultVecEE.byteSize (regs .x11) Layouts.Transcript.byteSize ∧
    Apart (regs .x10) Layouts.ResultVecEE.byteSize (m.getMem (regs .x11 + 328#64)) Layouts.Proof.byteSize

/-- Unless the slot holds `Err`, the point at its head a vector of `E`s. -/
def OkVec (env : Env) (regs : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (regs .x10) ≠ 18446744073709551615#64 → VecT env m' (regs .x10) 16

/-- The total postcondition: the transcript `TranscriptAtT` and owned again, its proof's address kept, `OkVec`. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  TranscriptAtT env m' (regs .x11) ∧ OwnedT env m' (regs .x2) (regs .x11) ∧
    m'.getMem (regs .x11 + 328#64) = m.getMem (regs .x11 + 328#64) ∧ OkVec env regs m'

/-- **The total contract of `read_ood`**: `PreT` to `PostT`, writing at most the slot, the sponge and the stream
    offset (`TOut`, the partial contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (Spec.Whir.Transcript.TOut Layouts.ResultVecEE.byteSize)
    (Stop := AbortStop)

/-- What the run gives, from which `PostT` follows with the frame: the sponge `SpongeT`, `OkVec`. -/
def PostK (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x11) ∧ OkVec env regs m'

/-- `PreT`'s facts the parts carry whole. -/
structure Ctx (env : Env) (top : Word) (regs : Reg → Word) (m : MachineState) : Prop where
  tT : TranscriptAtT env m (regs .x11)
  tO : OwnedT env m top (regs .x11)
  wS : InWin env (regs .x10) 40
  aS : (regs .x10).toNat % 8 = 0
  oS : env.Owned m top (regs .x10) 40
  apST : Apart (regs .x10) 40 (regs .x11) Layouts.Transcript.byteSize
  apSP : Apart (regs .x10) 40 (m.getMem (regs .x11 + 328#64)) Layouts.Proof.byteSize

/-- What the parts keep of the memory: the frame, the code, the static data, the saved registers' slots, the
    transcript `TranscriptAtT` and owned, its proof's address. -/
def BaseM (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (M : MachineState) : Prop :=
  env.Frame top (NextScalar.Out 40 regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    TranscriptAtT env M (regs .x11) ∧ OwnedT env M top (regs .x11) ∧
    M.getMem (regs .x11 + 328#64) = m.getMem (regs .x11 + 328#64)

/-- The state before `grind_check`'s call (instruction 20): the registers, `BaseM`. -/
def AInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧ R .x18 = regs .x12 ∧
    R .x10 = regs .x11 ∧ R .x11 = 15#64 ∧
    R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    BaseM env ret top regs m M

/-- The state before `next_scalar`'s call (instruction 46): the registers, `BaseM`, the point a vector at
    `sp + 0`. -/
def CInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧
    R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    BaseM env ret top regs m M ∧ VecT env M (top + 18446744073709551536#64) 16

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- Two more words stored into the slot, at `24` and `32`, apart from the transcript, keep its sponge `SpongeT`. -/
theorem spongeT_two {env : Env} {M : MachineState} {a T v w : Word} (hw : InWin env a 40)
    (hT : SpongeT env M T) (hap : Apart a 40 T Layouts.Transcript.byteSize) (hlT : T.toNat + 360 < 2 ^ 64) :
    SpongeT env ((M.setMem (a + 24#64) v).setMem (a + 32#64) w) T := by
  have hlt := hw.lt
  unfold Apart at hap
  simp only [Layouts.Transcript.byteSize] at hap
  have e24 : (a + 24#64).toNat = a.toNat + 24 := toNat_add_ofNat (by omega)
  have e32 : (a + 32#64).toNat = a.toNat + 32 := toNat_add_ofNat (by omega)
  have e320 : (T + 320#64).toNat = T.toNat + 320 := toNat_add_ofNat (by omega)
  refine spongeT_of_get hT ?_ ?_
  · rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e32]; omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e24]; omega))]
  · rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e32, e320]; omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e24, e320]; omega))]

/-- A vector's header at `a` is kept by stores at `a + 24` and `a + 32`. -/
theorem vecT_keep2 {env : Env} {M : MachineState} {a v w : Word} (hw : InWin env a 40) (h : VecT env M a 16) :
    VecT env ((M.setMem (a + 24#64) v).setMem (a + 32#64) w) a 16 := by
  have hlt := hw.lt
  have e24 : (a + 24#64).toNat = a.toNat + 24 := toNat_add_ofNat (by omega)
  have e32 : (a + 32#64).toNat = a.toNat + 32 := toNat_add_ofNat (by omega)
  have hk : ∀ o : Nat, o ≤ 16 → ((M.setMem (a + 24#64) v).setMem (a + 32#64) w).getMem (a + BitVec.ofNat 64 o) =
      M.getMem (a + BitVec.ofNat 64 o) := fun o ho => by
    have e : (a + BitVec.ofNat 64 o).toNat = a.toNat + o := toNat_add_ofNat (by omega)
    rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e, e32]; omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e, e24]; omega))]
  have hn : env.next ((M.setMem (a + 24#64) v).setMem (a + 32#64) w) = env.next M := by
    rw [Tactic.next_setMem (hw.ne_next (by rw [e32]; omega) (by rw [e32]; omega)),
      Tactic.next_setMem (hw.ne_next (by rw [e24]; omega) (by rw [e24]; omega))]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2.keep (hk 0 (by omega)) (hk 8 (by omega)) (by rw [hn]), ?_⟩
  simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap]
  rw [hk 16 (by omega), hk 0 (by omega)]
  exact h3

/-- A word of the frame at or above `next_scalar`'s result slot's end, or below the slot, is not one it writes: its
    slot is `[top - 56, top - 32)`, the transcript owned by the caller. -/
theorem not_nsOut {env : Env} {top a T : Word} {r : Reg → Word} {M : MachineState}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hnx : (env.next M).toNat ≤ env.heapEnd.toNat)
    (ha : top.toNat - 80 ≤ a.toNat) (ha' : a.toNat < top.toNat)
    (hs : a.toNat < (r .x10).toNat ∨ (r .x10).toNat + 24 ≤ a.toNat) (hT : r .x11 = T)
    (hO : T.toNat + 360 ≤ (env.next M).toNat ∨ top.toNat ≤ T.toNat) (hlT : T.toNat + 360 < 2 ^ 64) :
    ¬ NextScalar.Out Layouts.ResultE.byteSize r M a := by
  have hlay := env.layout
  have h336 : (T + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = T.toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  simp only [NextScalar.Out, InRange, hT, Layouts.ResultE.byteSize, Layouts.Sponge.byteSize, not_or]
  refine ⟨by omega, by omega, fun h => ?_⟩
  have := congrArg BitVec.toNat h; rw [h336] at this; omega

/-- A word of the frame is not one `grind_check` writes: the transcript's sponge and stream offset, owned by the
    caller. -/
theorem not_gcOut {env : Env} {top a T : Word} {r : Reg → Word} {M : MachineState}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hnx : (env.next M).toNat ≤ env.heapEnd.toNat)
    (ha : top.toNat - 80 ≤ a.toNat) (ha' : a.toNat < top.toNat) (hT : r .x10 = T)
    (hO : T.toNat + 360 ≤ (env.next M).toNat ∨ top.toNat ≤ T.toNat) (hlT : T.toNat + 360 < 2 ^ 64) :
    ¬ GrindCheck.Out r M a := by
  have hlay := env.layout
  have h336 : (T + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = T.toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  simp only [GrindCheck.Out, InRange, hT, Layouts.Sponge.byteSize, not_or]
  refine ⟨by omega, fun h => ?_⟩
  have := congrArg BitVec.toNat h; rw [h336] at this; omega

set_option rv_sym.heap true in
/-- From `next_scalar`'s call: `Ok` of the point and the value, or the error, into the slot; the return. -/
theorem tail_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN : Nat} (hnN : 80 + needN ≤ need)
    (hns : NextScalarT.specT env p L.nextScalar.idx needN)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out 40) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, CInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 46, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hBM := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2
  rv_introT hinv
  have hnM := hinv_13.1
  rv_symT hp stop [54] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)] using [hns]
  have hsT : SpongeT env m1 (regs .x11) := ⟨hret1_16, hret1_17, hret1_18, hret1_19⟩
  have hF1 := hret1_14
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  rv_symT hp with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  all_goals
    have hlay := env.layout
    have hlS := hwS.lt
    have hlT := hC.tT.2.1.lt
    have hnM' := hinv_13.2.1
    have hk := fun (a : Word) (h1 : top.toNat - 80 ≤ a.toNat) (h2 : a.toNat < top.toNat)
        (h3 : a.toNat < top.toNat - 56 ∨ top.toNat - 32 ≤ a.toNat) =>
      keep1_1 a (BitVec.le_def.2 (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
        (not_nsOut (by omega) hnM' h1 h2
          (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
              rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
          (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]) hinv_29 hlT)
    have hF2 : env.Frame top (NextScalar.Out 40 regs m) m m1 := by
      refine Env.Frame.trans hinv_13 hF1 (by tn) fun b hb => ?_
      simp only [NextScalar.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
        Layouts.ResultE.byteSize] at hb
      rcases hb with hb | hb | hb
      · rw [BitVec.toNat_add, BitVec.toNat_ofNat] at hb; exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb))))
    have hw24 : InWin env (regs .x10) 24 := hwS.sub (Nat.le_refl _) (by omega)
    have hap24 : Apart (regs .x10) 24 (regs .x11) Layouts.Transcript.byteSize := by
      have := hC.apST; unfold Apart at this ⊢; omega
    have o : ∀ k : Nat, k < 40 → NextScalar.Out 40 regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      Or.inl ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩
    have n : ∀ k : Nat, k < 40 → regs .x10 + BitVec.ofNat 64 k ≠ env.nextAddr := fun k hk => hwS.ne_next_add hk
    have o0 : NextScalar.Out 40 regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by omega⟩
    have n0 : regs .x10 ≠ env.nextAddr := hwS.ne_next (Nat.le_refl _) (by omega)
  -- `Ok`: the point and the value
  · simp only [Tactic.rf]; rw [hk _ (by tn) (by tn) (by tn)]; exact hinv_16
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    · rw [hk _ (by tn) (by tn) (by tn)]; exact hinv_17
    · rw [hk _ (by tn) (by tn) (by tn)]; exact hinv_18
    · rw [hk _ (by tn) (by tn) (by tn)]; exact hinv_19
    · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF2 o0 n0)
        (o 8 (by omega)) (n 8 (by omega))) (o 16 (by omega)) (n 16 (by omega))) (o 24 (by omega))
        (n 24 (by omega))) (o 32 (by omega)) (n 32 (by omega))
    · rv_closeT
    · exact spongeT_two hwS (sret_spongeT hw24 hsT hap24 hlT) hC.apST hlT
    · intro _
      obtain ⟨-, ⟨-, -, hb, hc⟩, hl⟩ := hV
      have e0 : rvCapAt (top + 18446744073709551536#64) = top + 18446744073709551536#64 := by
        simp only [rvCapAt, Layouts.RawVecInner.cap]; exact BitVec.add_zero _
      have e8 : rvPtrAt (top + 18446744073709551536#64) = top + 18446744073709551544#64 := by
        simp only [rvPtrAt, Layouts.RawVecInner.ptr, BitVec.add_assoc]; exact congrArg (top + ·) (by decide)
      have e16 : top + 18446744073709551536#64 + BitVec.ofNat 64 Layouts.Vec.len = top + 18446744073709551552#64 := by
        simp only [Layouts.Vec.len, BitVec.add_assoc]; exact congrArg (top + ·) (by decide)
      have e0' : top + 18446744073709551536#64 + BitVec.ofNat 64 Layouts.Vec.cap = top + 18446744073709551536#64 := by
        simp only [Layouts.Vec.cap]; exact BitVec.add_zero _
      rw [e0, e8] at hb
      rw [e0] at hc
      simp only [vecLen, vecCap, e16, e0'] at hl
      refine vecT_keep2 hwS (vecT_stores hw24 haS ?_ ?_ ?_)
      · rw [hk _ (by tn) (by tn) (by tn), hk _ (by tn) (by tn) (by tn)]; exact hb.mono hret1_14.1
      · rw [hk _ (by tn) (by tn) (by tn)]; exact hc
      · rw [hk _ (by tn) (by tn) (by tn), hk _ (by tn) (by tn) (by tn)]; exact hl
  -- `Err`
  · simp only [Tactic.rf]; rw [hk _ (by tn) (by tn) (by tn)]; exact hinv_16
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    · rw [hk _ (by tn) (by tn) (by tn)]; exact hinv_17
    · rw [hk _ (by tn) (by tn) (by tn)]; exact hinv_18
    · rw [hk _ (by tn) (by tn) (by tn)]; exact hinv_19
    · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF2 o0 n0) (o 8 (by omega)) (n 8 (by omega)))
        (o 16 (by omega)) (n 16 (by omega))
    · rv_closeT
    · exact sret_spongeT hw24 hsT hap24 hlT
    · intro h
      exfalso
      apply h
      have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
      have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
      rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e16]; omega)),
        MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e8]; omega)), MachineState.getMem_setMem_eq]

/-- A callee writing a result's slot of `n` bytes in the frame, the sponge and the stream offset misses the
    transcript's proof's address and the stream's words, the transcript and its proof owned by the caller. -/
theorem out_miss_frame {env : Env} {top T : Word} {r : Reg → Word} {M : MachineState} {n : Nat}
    (hlim : env.stackLimit.toNat ≤ (r .x10).toNat) (hs : (r .x10).toNat + n ≤ top.toNat) (hT : r .x11 = T)
    (hnx : (env.next M).toNat ≤ env.heapEnd.toNat) (hTr : TranscriptAtT env M T) (hO : OwnedT env M top T) :
    ¬ NextScalar.Out n r M (T + BitVec.ofNat 64 328) ∧
      ∀ k, (k = 8 ∨ k = 16) → ¬ NextScalar.Out n r M (M.getMem (T + 328#64) + BitVec.ofNat 64 k) := by
  have hlay := env.layout
  obtain ⟨_, hwT, hA, _, hQ, _⟩ := hTr
  obtain ⟨⟨hO1, hO2⟩, ⟨hP1, hP2⟩⟩ := hO
  have ha := hwT.lt
  have hq := hQ.lt
  unfold Apart at hA
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hA hq ha hO1 hO2 hP1 hP2
  have h336 : (T + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = T.toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  refine ⟨?_, fun k hk => ?_⟩ <;> simp only [NextScalar.Out, InRange, hT, Layouts.Sponge.byteSize, not_or] <;>
    refine ⟨?_, ?_, fun he => ?_⟩
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), h336] at this; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · have := congrArg BitVec.toNat he
    rw [toNat_add_ofNat (by omega), h336] at this; omega

/-- **`BaseM` across a call** from `sp` (`top - 80`) that writes a result's slot of `n` bytes in the frame below the
    saved registers' slots, the transcript's sponge and its stream offset, and leaves the sponge `SpongeT`. -/
theorem baseM_call {env : Env} {ret top : Word} {regs r : Reg → Word} {m M m2 : MachineState} {n : Nat}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 80 ≤ top.toNat)
    (hf : env.Frame (top + 18446744073709551536#64) (NextScalar.Out n r M) M m2) (hc : m2.code = M.code)
    (hs : env.Static m2) (hsT : SpongeT env m2 (regs .x11))
    (hx10 : top.toNat - 80 ≤ (r .x10).toNat) (hx10' : (r .x10).toNat + n ≤ top.toNat - 32)
    (hx11 : r .x11 = regs .x11) : BaseM env ret top regs m m2 := by
  obtain ⟨hF, hcM, -, h1, h2, h3, h4, hT, hO, hP⟩ := hB
  have hlay := env.layout
  have hnM := hF.2.1
  have hsp : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by tn
  have hO' : OwnedT env M (top + 18446744073709551536#64) (regs .x11) := hO.mono (by rw [hsp]; omega)
  have hms := out_miss_frame (n := n) (top := top) (by omega) (by omega) hx11 hnM hT hO
  have hTT := hT.frameS hsT hO' hf hnM (by rw [hsp]; omega) hms.1 hms.2
  have hlT := hT.2.1.lt
  have hO1 := hO.1
  simp only [Env.Owned, Layouts.Transcript.byteSize] at hO1 hlT
  have h336 : (regs .x11 + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = (regs .x11).toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  have hsl : ∀ c : Nat, 0 < c → c ≤ 32 → m2.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) := fun c hc0 hc1 => by
    have e : (top + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = top.toNat - c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine hf.getMem_above (by rw [hsp]; omega) (by rw [e, hsp]; omega) ?_
    simp only [NextScalar.Out, InRange, hx11, Layouts.Sponge.byteSize, not_or, e]
    refine ⟨by omega, by omega, fun h => ?_⟩
    have := congrArg BitVec.toNat h; rw [e, h336] at this; omega
  refine ⟨Env.Frame.trans hF hf (by rw [hsp]; omega) fun b hb => ?_, hc.trans hcM, hs, ?_, ?_, ?_, ?_, hTT.1,
    OwnedT.of_next hO hf.1 hTT.2.2, hTT.2.2.trans hP⟩
  · simp only [NextScalar.Out, InRange, hx11] at hb
    rcases hb with hb | hb | hb
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb))))
  · exact (hsl 8 (by omega) (by omega)).trans h1
  · exact (hsl 16 (by omega) (by omega)).trans h2
  · exact (hsl 24 (by omega) (by omega)).trans h3
  · exact (hsl 32 (by omega) (by omega)).trans h4

/-- The state on `grind_check`'s error (instruction 28): the registers, `-1` in `x12`, `BaseM`. -/
def EInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ R .x12 = 18446744073709551615#64 ∧
    R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    BaseM env ret top regs m M

set_option rv_sym.heap true in
/-- On `grind_check`'s error: the error into the slot, the return. -/
theorem err_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out 40) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 80 ≤ need) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, EInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 28, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  rv_introT hinv
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  rv_symT hp with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  all_goals
    have hlS := hwS.lt
    have hlT := hC.tT.2.1.lt
    have hsT : SpongeT env M (regs .x11) := ⟨hinv_20, hinv_21, hinv_22, hinv_23⟩
    have hw24 : InWin env (regs .x10) 24 := hwS.sub (Nat.le_refl _) (by omega)
    have hap24 : Apart (regs .x10) 24 (regs .x11) Layouts.Transcript.byteSize := by
      have := hC.apST; unfold Apart at this ⊢; omega
    have o : ∀ k : Nat, k < 40 → NextScalar.Out 40 regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      Or.inl ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩
    have n : ∀ k : Nat, k < 40 → regs .x10 + BitVec.ofNat 64 k ≠ env.nextAddr := fun k hk => hwS.ne_next_add hk
    have o0 : NextScalar.Out 40 regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by omega⟩
    have n0 : regs .x10 ≠ env.nextAddr := hwS.ne_next (Nat.le_refl _) (by omega)
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hinv_13 o0 n0) (o 8 (by omega)) (n 8 (by omega)))
      (o 16 (by omega)) (n 16 (by omega))
  · exact (sret_spongeT hw24 hsT hap24 hlT).2.2.1
  · exact (sret_spongeT hw24 hsT hap24 hlT).2.2.2
  · intro h; exact absurd rfl h

set_option rv_sym.heap true in
/-- From `grind_check`'s call: its error into the slot and the return, or `samples` and on to `next_scalar`'s call. -/
theorem mid_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG needS needN : Nat} (hnG : 80 + needG ≤ need) (hnS : 80 + needS ≤ need)
    (hnN : 80 + needN ≤ need) (hgc : GrindCheckT.specT env p L.grindCheck.idx needG)
    (hsa : SamplesT.specT env p L.samples.idx needS) (hns : NextScalarT.specT env p L.nextScalar.idx needN)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out 40) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, AInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 20, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hBM := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rv_introT hinv
  have hnM := hinv_16.1
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  rv_symT hp stop [24] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)] using [hgc]
  have hT1 : TranscriptAtT env m1 (regs .x11) :=
    ⟨⟨hret1_16, hret1_17, hret1_18, hret1_19⟩, hret1_20, hret1_21, hret1_22, hret1_23, hret1_24⟩
  have hO1 : OwnedT env m1 (top + 18446744073709551536#64) (regs .x11) := ⟨⟨hret1_25, hret1_26⟩, ⟨hret1_27, hret1_28⟩⟩
  have hF1 := hret1_14
  have hP1 := hret1_29
  have hc1 := hret1_30
  have hs1 := hret1_15
  have hlay := env.layout
  have hlT := hC.tT.2.1.lt
  have hnM' := hinv_16.2.1
  have hk1 := fun (a : Word) (h1 : top.toNat - 80 ≤ a.toNat) (h2 : a.toNat < top.toNat) =>
    keep1_1 a (BitVec.le_def.2 (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
      (not_gcOut (by omega) hnM' h1 h2 (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte])
        hinv_32 hlT)
  have hF1' : env.Frame top (NextScalar.Out 40 regs m) m m1 := by
    refine Env.Frame.trans hinv_16 hF1 (by tn) fun b hb => ?_
    simp only [GrindCheck.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] at hb
    rcases hb with hb | hb
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb))))
  rv_symT hp stop [28, 36] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  -- `Ok`: `samples`, on to `next_scalar`'s call
  · have hO0 : OwnedT env m1 top (regs .x11) := OwnedT.of_next hBM.2.2.2.2.2.2.2.2.1 hF1.1 hP1
    have hnM1 := hF1'.2.1
    have hBM1 : BaseM env ret top regs m m1 := ⟨hF1', hc1.trans hinv_17, hs1,
      by rw [hk1 _ (by tn) (by tn)]; exact hinv_19, by rw [hk1 _ (by tn) (by tn)]; exact hinv_20,
      by rw [hk1 _ (by tn) (by tn)]; exact hinv_21, by rw [hk1 _ (by tn) (by tn)]; exact hinv_22, hT1, hO0,
      hP1.trans hinv_36⟩
    rv_symT hp stop [46] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)] using [hsa]
    have hsT2 : SpongeT env m1 (regs .x11) := ⟨hret1_23, hret1_24, hret1_25, hret1_26⟩
    refine tail_ok env p i L hp hL hnN hns hstop hk hstk hnx hal hW hC _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, baseM_call hBM1 (by omega) hret1_14 hret1_27 hret1_15 hsT2
        (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; tn)
        (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, Layouts.Vec.byteSize]; tn)
        (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]),
      ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩⟩
    iterate 12 · rv_closeT
  -- `Err`: the error into the slot
  · have hO0 : OwnedT env m1 top (regs .x11) := OwnedT.of_next hBM.2.2.2.2.2.2.2.2.1 hF1.1 hP1
    refine err_ok env p i L hp hk hstk (by omega) hnx hal hW hC _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hF1', hc1.trans hinv_17, hs1, ?_, ?_, ?_, ?_, hT1, hO0, hP1.trans hinv_36⟩
    iterate 12 · rv_closeT
    · rw [hk1 _ (by tn) (by tn)]; exact hinv_19
    · rw [hk1 _ (by tn) (by tn)]; exact hinv_20
    · rw [hk1 _ (by tn) (by tn)]; exact hinv_21
    · rw [hk1 _ (by tn) (by tn)]; exact hinv_22

set_option rv_sym.heap true in
/-- **`read_ood` returns `PostK`.** -/
theorem kept (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needG needS needN : Nat} (hnG : 80 + needG ≤ need) (hnS : 80 + needS ≤ need)
    (hnN : 80 + needN ≤ need) (hgc : GrindCheckT.specT env p L.grindCheck.idx needG)
    (hsa : SamplesT.specT env p L.samples.idx needS) (hns : NextScalarT.specT env p L.nextScalar.idx needN) :
    HoldsT env p i need (PreT env) (PostK env) (NextScalar.Out 40) (Stop := AbortStop) := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  have hC : Ctx env top regs m := hpre_2 ▸ ⟨⟨⟨hpre_6, hpre_7, hpre_8, hpre_9⟩, hpre_10, hpre_11, hpre_12, hpre_13, hpre_14⟩,
    ⟨⟨hpre_15, hpre_16⟩, ⟨hpre_17, hpre_18⟩⟩, hpre_19, hpre_20, ⟨hpre_21, hpre_22⟩, hpre_23, hpre_24⟩
  clear hpre_6 hpre_7 hpre_8 hpre_9 hpre_10 hpre_11 hpre_12 hpre_13 hpre_14 hpre_15 hpre_16 hpre_17 hpre_18 hpre_19
    hpre_20 hpre_21 hpre_22 hpre_23 hpre_24
  rv_symT hp stop [20] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  refine mid_ok env p i L hp hL hnG hnS hnN hgc hsa hns hstop hk hpre_3 hpre_5 hpre_25 hpre_26 hC _ _
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 18 · rv_closeT
  iterate 4 simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).1
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.1
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.2

/-- `NextScalar.Out 40` misses the proof's address and the stream's words, the slot apart from the transcript and its
    proof. -/
theorem out_miss {env : Env} {regs : Reg → Word} {m : MachineState} (h : PreT env regs m) :
    ¬ NextScalar.Out 40 regs m (regs .x11 + BitVec.ofNat 64 328) ∧
      ∀ k, (k = 8 ∨ k = 16) → ¬ NextScalar.Out 40 regs m (m.getMem (regs .x11 + 328#64) + BitVec.ofNat 64 k) := by
  obtain ⟨⟨_, hT, hA, _, hQ, _⟩, _, hW, _, _, hR, hP⟩ := h
  have ha := hT.lt
  have hq := hQ.lt
  have hw := hW.lt
  unfold Apart at hA hR hP
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize, Layouts.ResultVecEE.byteSize] at *
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

/-- **`read_ood` is total**, from `kept` and `TOut`'s frame (`TranscriptAtT.frameS`). -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needG needS needN : Nat} (hnG : 80 + needG ≤ need) (hnS : 80 + needS ≤ need)
    (hnN : 80 + needN ≤ need) (hgc : GrindCheckT.specT env p L.grindCheck.idx needG)
    (hsa : SamplesT.specT env p L.samples.idx needS) (hns : NextScalarT.specT env p L.nextScalar.idx needN) :
    specT env p i need :=
  Isa.TContract.mono (kept env p i L hp hL hnG hnS hnN hgc hsa hns) (fun _ _ _ _ h => h)
    (fun _ top regs m _ _ ⟨⟨he, hs, _, hn, hP, _⟩, _⟩ ⟨⟨ha, hf, hst', hK, hV⟩, hc⟩ => by
      have hT := hP.1.frameS hK (he.2 ▸ hP.2.1) hf hn (by omega) (out_miss hP).1 (out_miss hP).2
      exact ⟨⟨ha, hf, hst', hT.1, he.2 ▸ hT.2.1, hT.2.2, hV⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Whir.ReadOodT

/-- info: 'Rv64mc.Proof.Whir.ReadOodT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.ReadOodT.total
