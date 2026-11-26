/-
  Rv64mc.Proof.Transcript.ScalarsIterT

  `next_scalars`' iterator (`<GenericShunt<Map<Range<usize>, next_scalars::{closure}>, _> as Iterator>::next`) is
  total (`specT`): from the shunt at `a1` (the transcript's address, the range's start and end, the residual's
  address) owned, in a window and apart from the transcript and its proof, the transcript `TranscriptAtT`
  (`TranscriptReprT`) owned with its proof (`OwnedT`), and the result's slot and the residual in windows apart from
  the transcript and its proof, it returns with the transcript `TranscriptAtT` and owned again, its proof's address
  kept, and, where the result is `Some`, the range not exhausted at entry and its start advanced by one, writing at most
  `ScalarsIter.Out`, or ends the run with `a0 = 2` where `next_scalar` does. Safety only: the partial contract's value
  (`ScalarsIter.lean`) is `next_scalar`'s functional one. The start advanced is the measure of `next_scalars`' loop.

  Cut at `next_scalar`'s call (`MidInv`, `mid`) and return (`TailInv`, `tail`) and at the exhausted range's branch
  (`NoneInv`, `none_ok`); `kept` steps the prologue with `PreT`'s objects held whole in `Ctx`, so that the executor's
  `omega` does not split their disjunctions, and proves the parts' invariants through frames (`TranscriptAtT.frame`,
  `frameF`), not by reading the stores.

  ## Main definitions

  * `PreT`, `Advanced`, `PostT`, `specT`, `PostK`, `Ctx`, `TailInv`, `MidInv`, `NoneInv`

  ## Main results

  * `out_slot`, `out_res`, `tail`, `mid`, `ne_owned`, `apart_ne`, `slots3`, `none_ok`, `kept`, `out_miss`, `total`
-/

import Rv64mc.Proof.Transcript.NextScalarT
import Rv64mc.Proof.Whir.Mem
import Rv64mc.Spec.Transcript.ScalarsIter
import Rv64mc.Gen.Tmpl.Core.Iter.Adapters.GenericShuntMapRangeUsizHcc804615.AsIterator.Next

namespace Rv64mc.Proof.Transcript.ScalarsIterT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Gen.Core.Iter.Adapters.GenericShuntMapRangeUsizHcc804615.AsIterator.Next (Link tmpl)

/-- The total precondition: the transcript (the shunt's first word) `TranscriptAtT` and owned with its proof; the
    shunt owned, in a window, 8-byte aligned, apart from the transcript and its proof; the result's slot and the
    residual (the shunt's fourth word) in windows, 8-byte aligned, apart from the transcript and its proof, the slot
    also apart from the shunt. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAtT env m (m.getMem (regs .x11)) ∧ OwnedT env m (regs .x2) (m.getMem (regs .x11)) ∧
    InWin env (regs .x11) 32 ∧ (regs .x11).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x11) 32 ∧
    Apart (regs .x11) 32 (m.getMem (regs .x11)) Layouts.Transcript.byteSize ∧
    Apart (regs .x11) 32 (m.getMem (m.getMem (regs .x11) + 328#64)) Layouts.Proof.byteSize ∧
    InWin env (regs .x10) Layouts.OptionE.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    env.Owned m (regs .x2) (regs .x10) Layouts.OptionE.byteSize ∧
    Apart (regs .x10) Layouts.OptionE.byteSize (m.getMem (regs .x11)) Layouts.Transcript.byteSize ∧
    Apart (regs .x10) Layouts.OptionE.byteSize (m.getMem (m.getMem (regs .x11) + 328#64)) Layouts.Proof.byteSize ∧
    Apart (regs .x10) Layouts.OptionE.byteSize (regs .x11) 32 ∧
    InWin env (m.getMem (regs .x11 + 24#64)) 16 ∧ (m.getMem (regs .x11 + 24#64)).toNat % 8 = 0 ∧
    env.Owned m (regs .x2) (m.getMem (regs .x11 + 24#64)) 16 ∧
    Apart (m.getMem (regs .x11 + 24#64)) 16 (m.getMem (regs .x11)) Layouts.Transcript.byteSize ∧
    Apart (m.getMem (regs .x11 + 24#64)) 16 (m.getMem (m.getMem (regs .x11) + 328#64)) Layouts.Proof.byteSize ∧
    Apart (m.getMem (regs .x11 + 24#64)) 16 (regs .x11) 32

/-- Where the result is `Some` (its tag not `None`'s `0`), the range was not exhausted and its start advanced. -/
def Advanced (regs : Reg → Word) (m : MachineState) (m' : MachineState) : Prop :=
  m'.getMem (regs .x10) ≠ 0#64 →
    (m.getMem (regs .x11 + 8#64)).toNat < (m.getMem (regs .x11 + 16#64)).toNat ∧
      m'.getMem (regs .x11 + 8#64) = m.getMem (regs .x11 + 8#64) + 1#64

/-- The total postcondition: the transcript `TranscriptAtT` and owned again, its proof's address kept, and
    `Advanced`. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  TranscriptAtT env m' (m.getMem (regs .x11)) ∧ OwnedT env m' (regs .x2) (m.getMem (regs .x11)) ∧
    m'.getMem (m.getMem (regs .x11) + 328#64) = m.getMem (m.getMem (regs .x11) + 328#64) ∧ Advanced regs m m'

/-- **The total contract of `next_scalars`' iterator**: `PreT` to `PostT`, writing at most the slot, the start, the
    sponge, the stream offset and the residual (`ScalarsIter.Out`), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) ScalarsIter.Out (Stop := AbortStop)

/-- What the run gives, from which `PostT` follows with the frame: the sponge `SpongeT`, and `Advanced`. -/
def PostK (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (m.getMem (regs .x11)) ∧ Advanced regs m m'

/-- The facts the iterator's parts carry whole, so that the executor's `omega` does not split them: the transcript and
    `PreT`'s objects, at the entry's memory. -/
structure Ctx (env : Env) (top : Word) (regs : Reg → Word) (m : MachineState) : Prop where
  tT : TranscriptAtT env m (m.getMem (regs .x11))
  tO : OwnedT env m top (m.getMem (regs .x11))
  wA : InWin env (regs .x11) 32
  aA : (regs .x11).toNat % 8 = 0
  oA : env.Owned m top (regs .x11) 32
  apAT : Apart (regs .x11) 32 (m.getMem (regs .x11)) Layouts.Transcript.byteSize
  apAP : Apart (regs .x11) 32 (m.getMem (m.getMem (regs .x11) + 328#64)) Layouts.Proof.byteSize
  wS : InWin env (regs .x10) Layouts.OptionE.byteSize
  aS : (regs .x10).toNat % 8 = 0
  oS : env.Owned m top (regs .x10) Layouts.OptionE.byteSize
  apST : Apart (regs .x10) Layouts.OptionE.byteSize (m.getMem (regs .x11)) Layouts.Transcript.byteSize
  apSP : Apart (regs .x10) Layouts.OptionE.byteSize (m.getMem (m.getMem (regs .x11) + 328#64)) Layouts.Proof.byteSize
  apSA : Apart (regs .x10) Layouts.OptionE.byteSize (regs .x11) 32
  wR : InWin env (m.getMem (regs .x11 + 24#64)) 16
  aR : (m.getMem (regs .x11 + 24#64)).toNat % 8 = 0
  oR : env.Owned m top (m.getMem (regs .x11 + 24#64)) 16
  apRT : Apart (m.getMem (regs .x11 + 24#64)) 16 (m.getMem (regs .x11)) Layouts.Transcript.byteSize
  apRP : Apart (m.getMem (regs .x11 + 24#64)) 16 (m.getMem (m.getMem (regs .x11) + 328#64)) Layouts.Proof.byteSize
  apRA : Apart (m.getMem (regs .x11 + 24#64)) 16 (regs .x11) 32

/-- A word of the result's slot is in `ScalarsIter.Out`. -/
theorem out_slot {regs : Reg → Word} {m : MachineState} {k : Nat} (hk : k < 24)
    (hw : (regs .x10).toNat + 24 < 2 ^ 64) : ScalarsIter.Out regs m (regs .x10 + BitVec.ofNat 64 k) :=
  Or.inl (by unfold InRange; simp only [Layouts.OptionE.byteSize]; rw [toNat_add_ofNat (by omega)]; omega)

/-- A word of the residual is in `ScalarsIter.Out`. -/
theorem out_res {regs : Reg → Word} {m : MachineState} {k : Nat} (hk : k < 16)
    (hw : (m.getMem (regs .x11 + 24#64)).toNat + 16 < 2 ^ 64) :
    ScalarsIter.Out regs m (m.getMem (regs .x11 + 24#64) + BitVec.ofNat 64 k) :=
  Or.inr (Or.inr (Or.inr (Or.inr (by
    unfold InRange ScalarsIter.shuntRes; rw [toNat_add_ofNat (by omega)]; omega))))

set_option hygiene false in
/-- A read through a store apart from it, by the addresses as numbers (`hap`, `hlS`, `hlR`, `hlT` in the context). -/
local macro "rd_ne" : tactic => `(tactic| (
  intro e; have e' := congrArg BitVec.toNat e; (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at e'); omega))

/-- The state after `next_scalar`'s return (instruction 32): the registers kept, the frame, the code, the static data,
    the saved registers' slots, the sponge `SpongeT`, the start advanced from below the end. -/
def TailInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551568#64 ∧ R .x8 = regs .x10 ∧ R .x9 = m.getMem (regs .x11 + 24#64) ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top (ScalarsIter.Out regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ SpongeT env M (m.getMem (regs .x11)) ∧
    M.getMem (regs .x11 + 8#64) = m.getMem (regs .x11 + 8#64) + 1#64 ∧
    (m.getMem (regs .x11 + 8#64)).toNat < (m.getMem (regs .x11 + 16#64)).toNat

-- one `rv_symT` run over both outcomes of the result's tag, each with its three stores, does not fit the default
set_option maxHeartbeats 1000000 in
set_option rv_sym.heap true in
/-- From `next_scalar`'s return: the result's tag read, `Some` of the scalar or the error into the residual. -/
theorem tail (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) ScalarsIter.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnN : 48 ≤ need) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, TailInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 32, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  rv_introT hinv
  have hwS := hC.wS
  have haS := hC.aS
  have hwR := hC.wR
  have haR := hC.aR
  have hST := hC.apST
  have hRT := hC.apRT
  have hSA := hC.apSA
  have hoS := hC.oS
  have hoR := hC.oR
  have hRA := hC.apRA
  have hwT := hC.tT.2.1
  have hlS := hwS.lt
  have hlR := hwR.lt
  rv_symT hp with [(by omega : env.stackLimit.toNat + 48 ≤ top.toNat)]
  -- `Some`: the value and the tag stored into the slot
  all_goals
    have hlT := hwT.lt
    have hap := hST
    have hap' := hRT
    unfold Apart at hap hap'
    simp only [Layouts.OptionE.byteSize, Layouts.Transcript.byteSize] at hap hap' hlS hlT
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hinv_14 (out_slot (k := 8) (by omega) hlS)
      (hwS.ne_next_add (o := 8) (by decide))) (out_slot (k := 16) (by omega) hlS)
      (hwS.ne_next_add (o := 16) (by decide)))
      (by simpa using out_slot (m := m) (k := 0) (by omega) hlS) (hwS.ne_next (Nat.le_refl _) (by simp only [Layouts.OptionE.byteSize]; omega))
  · rw [MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne]
    · exact hinv_22
    all_goals rd_ne
  · rw [MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne]
    · exact hinv_23
    all_goals rd_ne
  · intro _
    refine ⟨hinv_25, ?_⟩
    have hlA := hC.wA.lt
    unfold Apart at hSA
    simp only [Layouts.OptionE.byteSize] at hSA
    rw [MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne]
    · exact hinv_24
    all_goals rd_ne
  -- `None`: the error stored into the residual, the tag into the slot
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hinv_14
      (by simpa using out_res (m := m) (regs := regs) (k := 0) (by omega) hlR)
      (hwR.ne_next (Nat.le_refl _) (by omega))) (out_res (k := 8) (by omega) hlR)
      (hwR.ne_next_add (o := 8) (by decide)))
      (by simpa using out_slot (m := m) (k := 0) (by omega) hlS) (hwS.ne_next (Nat.le_refl _) (by simp only [Layouts.OptionE.byteSize]; omega))
  · rw [MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne]
    · exact hinv_22
    all_goals rd_ne
  · rw [MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne, MachineState.getMem_setMem_ne]
    · exact hinv_23
    all_goals rd_ne
  · intro h; exact absurd rfl h

/-- The state before `next_scalar`'s call (instruction 28): the registers, the frame, the code, the static data, the
    saved registers' slots, the transcript `TranscriptAtT` and owned, the start advanced from below the end. -/
def MidInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551568#64 ∧ R .x8 = regs .x10 ∧ R .x9 = m.getMem (regs .x11 + 24#64) ∧
    R .x10 = top + 18446744073709551568#64 ∧ R .x11 = m.getMem (regs .x11) ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top (ScalarsIter.Out regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧
    TranscriptAtT env M (m.getMem (regs .x11)) ∧ OwnedT env M top (m.getMem (regs .x11)) ∧
    M.getMem (regs .x11 + 8#64) = m.getMem (regs .x11 + 8#64) + 1#64 ∧
    (m.getMem (regs .x11 + 8#64)).toNat < (m.getMem (regs .x11 + 16#64)).toNat

set_option hygiene false in
/-- A saved register's slot of the frame is kept by `next_scalar`, which writes its result's slot, the sponge and the
    stream offset. -/
local macro "slot_keep" : tactic => `(tactic| (
  rw [keep1_1 _ (BitVec.le_def.2 (by simp only [hsp, h8, h16, h24]; omega)) (by
    simp only [NextScalar.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, hsp,
      Layouts.ResultE.byteSize, Layouts.Sponge.byteSize, not_or]
    refine ⟨by simp only [h8, h16, h24]; omega, by simp only [h8, h16, h24]; omega, fun h => ?_⟩
    have := congrArg BitVec.toNat h
    simp only [h8, h16, h24, h336] at this
    omega)]))

set_option rv_sym.heap true in
/-- From `next_scalar`'s call to the return. -/
theorem mid (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN : Nat} (hnN : 48 + needN ≤ need) (hns : NextScalarT.specT env p L.nextScalar.idx needN)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostK env) ScalarsIter.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, MidInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 28, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hT := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hO := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rv_introT hinv
  have hoA := hC.oA
  rv_symT hp stop [32] with [hL, (by omega : env.stackLimit.toNat + 48 ≤ top.toNat)] using [hns]
  refine tail env p i L hp hk hstk (by omega) hnx hal hW hC _ _ ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 13 · rv_closeT
  all_goals
    have hsp : (top + 18446744073709551568#64).toNat = top.toNat - 48 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hx := hO.1.1
    have hx2 := hO.1.2
    have := env.layout
    have := hinv_16.2.1
    simp only [Layouts.Transcript.byteSize] at hx hx2
    have h336 : (m.getMem (regs .x11) + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat =
        (m.getMem (regs .x11)).toNat + 336 :=
      toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  · refine Env.Frame.trans hinv_16 hret1_14 (by omega) fun b hb => ?_
    simp only [NextScalar.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, hsp,
      Layouts.ResultE.byteSize] at hb
    rcases hb with hb | hb | hb
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))))
  · rw [hret1_30, hinv_17]
  · exact hret1_15
  · slot_keep; exact hinv_19
  · slot_keep; exact hinv_20
  · slot_keep; exact hinv_21
  · exact ⟨hret1_16, hret1_17, hret1_18, hret1_19⟩
  · have hlA := hC.wA.lt
    have hap := hC.apAT
    unfold Apart at hap
    simp only [Layouts.Transcript.byteSize] at hap
    have h8a : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
    have hk2 : (regs .x11 + 8#64).toNat < (env.next M).toNat ∨
        (top + 18446744073709551568#64).toNat ≤ (regs .x11 + 8#64).toNat := by
      have := hinv_16.1
      rw [h8a, hsp]
      rcases hoA.1 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hoA1 := hoA.1
    rw [keep1_2 _ hk2 (by
      simp only [NextScalar.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, hsp, h8a,
        Layouts.ResultE.byteSize, Layouts.Sponge.byteSize, not_or]
      refine ⟨by omega, by omega, fun h => ?_⟩
      have := congrArg BitVec.toNat h
      rw [h8a, h336] at this
      omega)]
    exact hinv_35
  · exact hinv_36

/-- A stack word below a caller's stack top is not a word of an object the caller owns. -/
theorem ne_owned {env : Env} {m : MachineState} {top x a : Word} {n o : Nat} (ho : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat ≤ x.toNat) (hx : x.toNat < top.toNat)
    (hon : o < n) : x ≠ a + BitVec.ofNat 64 o := by
  intro e
  have e' := congrArg BitVec.toNat e
  have h2 := ho.2
  have := env.layout
  rw [toNat_add_ofNat (by omega)] at e'
  rcases ho.1 with h | h <;> omega

/-- Words of two apart objects are different words. -/
theorem apart_ne {a b : Word} {n k i j : Nat} (h : Apart a n b k) (ha : a.toNat + n < 2 ^ 64)
    (hb : b.toNat + k < 2 ^ 64) (hi : i < n) (hj : j < k) : b + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 i := by
  intro e
  have e' := congrArg BitVec.toNat e
  rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)] at e'
  unfold Apart at h
  omega

/-- The prologue's three saved registers' slots, read back. -/
theorem slots3 {m : MachineState} {top a b c : Word} :
    (((m.setMem (top + 18446744073709551608#64) a).setMem (top + 18446744073709551600#64) b).setMem
        (top + 18446744073709551592#64) c).getMem (top + 18446744073709551608#64) = a ∧
    (((m.setMem (top + 18446744073709551608#64) a).setMem (top + 18446744073709551600#64) b).setMem
        (top + 18446744073709551592#64) c).getMem (top + 18446744073709551600#64) = b ∧
    (((m.setMem (top + 18446744073709551608#64) a).setMem (top + 18446744073709551600#64) b).setMem
        (top + 18446744073709551592#64) c).getMem (top + 18446744073709551592#64) = c := by
  refine ⟨?_, ?_, MachineState.getMem_setMem_eq⟩
  · rewrite [MachineState.getMem_setMem_ne (Rv64mc.Proof.Whir.slot_ne (by decide)),
      MachineState.getMem_setMem_ne (Rv64mc.Proof.Whir.slot_ne (by decide))]
    exact MachineState.getMem_setMem_eq
  · rewrite [MachineState.getMem_setMem_ne (Rv64mc.Proof.Whir.slot_ne (by decide))]
    exact MachineState.getMem_setMem_eq

/-- The state on an exhausted range (instruction 50): the registers kept, the frame, the code, the static data, the
    saved registers' slots, the sponge `SpongeT`. -/
def NoneInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551568#64 ∧ R .x8 = regs .x10 ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top (ScalarsIter.Out regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ SpongeT env M (m.getMem (regs .x11))

set_option rv_sym.heap true in
/-- On an exhausted range: `None` stored into the slot. -/
theorem none_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) ScalarsIter.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnN : 48 ≤ need) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, NoneInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 50, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  rv_introT hinv
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  have hlS := hwS.lt
  rv_symT hp with [(by omega : env.stackLimit.toNat + 48 ≤ top.toNat)]
  all_goals
    have hlT := hC.tT.2.1.lt
    have hap := hC.apST
    unfold Apart at hap
    simp only [Layouts.OptionE.byteSize, Layouts.Transcript.byteSize] at hap hlS hlT
  · exact Tactic.frame_out hinv_13 (by simpa using out_slot (m := m) (k := 0) (by omega) hlS)
      (hwS.ne_next (Nat.le_refl _) (by simp only [Layouts.OptionE.byteSize]; omega))
  · rw [MachineState.getMem_setMem_ne]
    · exact hinv_21
    rd_ne
  · rw [MachineState.getMem_setMem_ne]
    · exact hinv_22
    rd_ne
  · intro h; exact absurd rfl h

set_option rv_sym.heap true in
/-- **The iterator returns `PostK`.** -/
theorem kept (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needN : Nat} (hnN : 48 + needN ≤ need) (hns : NextScalarT.specT env p L.nextScalar.idx needN) :
    HoldsT env p i need (PreT env) (PostK env) ScalarsIter.Out (Stop := AbortStop) := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 48 ≤ top.toNat)]
  have hC : Ctx env top regs m := hpre_2 ▸ ⟨⟨⟨hpre_6, hpre_7, hpre_8, hpre_9⟩, hpre_10, hpre_11, hpre_12, hpre_13, hpre_14⟩,
    ⟨⟨hpre_15, hpre_16⟩, ⟨hpre_17, hpre_18⟩⟩, hpre_19, hpre_20, ⟨hpre_21, hpre_22⟩, hpre_23, hpre_24, hpre_25,
    hpre_26, ⟨hpre_27, hpre_28⟩, hpre_29, hpre_30, hpre_31, hpre_32, hpre_33, ⟨hpre_34, hpre_35⟩, hpre_36, hpre_37, hpre_38⟩
  clear hpre_6 hpre_7 hpre_8 hpre_9 hpre_10 hpre_11 hpre_12 hpre_13 hpre_14 hpre_15 hpre_16 hpre_17 hpre_18 hpre_19
    hpre_20 hpre_21 hpre_22 hpre_23 hpre_24 hpre_25 hpre_26 hpre_27 hpre_28 hpre_29 hpre_30 hpre_31 hpre_32 hpre_33
    hpre_34 hpre_35 hpre_36 hpre_37 hpre_38
  have hwA := hC.wA
  have haA := hC.aA
  have hoA := hC.oA
  rv_symT hp stop [28, 50] with [hL, (by omega : env.stackLimit.toNat + 48 ≤ top.toNat)]
  · clear hc
    refine none_ok env p i L hp hk hpre_3 (by omega) hpre_5 hpre_39 hpre_40 hC _ _ ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    iterate 15 · rv_closeT
    · exact slots3.1
    · exact slots3.2.1
    · exact slots3.2.2
    · refine (hC.tT.frameF hC.tO ?_ hpre_5 (by omega)).1.1
      rv_closeT
  · refine mid env p i L hp hL hnN hns hstop hk hpre_3 hpre_5 hpre_39 hpre_40 hC _ _ ?_
    have hlT := hC.tT.2.1.lt
    have hlP := hC.tT.2.2.2.2.1.lt
    have hlA := hC.wA.lt
    have hF : ∀ M, env.Frame top Tactic.F m M → env.Frame top (fun b => b = regs .x11 + 8#64) m
        (M.setMem (regs .x11 + 8#64) (m.getMem (regs .x11 + 8#64) + 1#64)) := fun M h =>
      Tactic.frame_out (Env.Frame.trans (Env.Frame.refl hpre_5) h (Nat.le_refl _) fun _ h => h.elim) rfl
        (hwA.ne_next_add (o := 8) (by decide))
    have hout : ∀ k, (k = 0 ∨ k = 320 ∨ k = 328) →
        ¬ (m.getMem (regs .x11) + BitVec.ofNat 64 k = regs .x11 + 8#64) := fun k hk =>
      apart_ne hC.apAT hlA hlT (by decide) (by simp only [Layouts.Transcript.byteSize]; omega)
    have hq : ∀ k, (k = 8 ∨ k = 16) →
        ¬ (m.getMem (m.getMem (regs .x11) + 328#64) + BitVec.ofNat 64 k = regs .x11 + 8#64) := fun k hk =>
      apart_ne hC.apAP hlA hlP (by decide) (by simp only [Layouts.Proof.byteSize]; omega)
    have h8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    iterate 15 · rv_closeT
    · refine Tactic.frame_out ?_ (Or.inr (Or.inl rfl)) (hwA.ne_next_add (o := 8) (by decide))
      rv_closeT
    · rv_closeT
    · rv_closeT
    · rewrite [MachineState.getMem_setMem_ne (ne_owned hC.oA hpre_5 (by omega) (by omega) (by decide))]
      exact slots3.1
    · rewrite [MachineState.getMem_setMem_ne (ne_owned hC.oA hpre_5 (by omega) (by omega) (by decide))]
      exact slots3.2.1
    · rewrite [MachineState.getMem_setMem_ne (ne_owned hC.oA hpre_5 (by omega) (by omega) (by decide))]
      exact slots3.2.2
    · refine (hC.tT.frame hC.tO (hF _ ?_) hpre_5 (by omega) hout hq).1
      rv_closeT
    · refine (hC.tT.frame hC.tO (hF _ ?_) hpre_5 (by omega) hout hq).2.1
      rv_closeT
    · exact MachineState.getMem_setMem_eq
    · exact BitVec.lt_def.mp hc

/-- `ScalarsIter.Out` misses the proof's address and the stream's words: the slot, the shunt and the residual apart
    from the transcript and its proof, the proof apart from the transcript. -/
theorem out_miss {env : Env} {regs : Reg → Word} {m : MachineState} (h : PreT env regs m) :
    ¬ ScalarsIter.Out regs m (m.getMem (regs .x11) + BitVec.ofNat 64 328) ∧
      ∀ k, (k = 8 ∨ k = 16) →
        ¬ ScalarsIter.Out regs m (m.getMem (m.getMem (regs .x11) + 328#64) + BitVec.ofNat 64 k) := by
  obtain ⟨⟨_, hT, hA, _, hQ, _⟩, _, hwA, _, _, hAT, hAP, _, _, _, hST, hSP, _, hwR, _, _, hRT, hRP, _⟩ := h
  have ha := hT.lt
  have hq := hQ.lt
  have hs := hwA.lt
  have hr := hwR.lt
  unfold Apart at hA hAT hAP hST hSP hRT hRP
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize, Layouts.OptionE.byteSize] at *
  have h336 : (m.getMem (regs .x11) + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat =
      (m.getMem (regs .x11)).toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  have h8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
  refine ⟨?_, fun k hk => ?_⟩ <;>
    simp only [ScalarsIter.Out, ScalarsIter.shuntT, ScalarsIter.shuntRes, InRange, Layouts.Sponge.byteSize,
      Layouts.OptionE.byteSize, not_or] <;>
    refine ⟨?_, fun he => ?_, ?_, fun he => ?_, ?_⟩
  all_goals first
    | (have := congrArg BitVec.toNat he
       rw [toNat_add_ofNat (by omega)] at this
       first | rw [h8] at this | rw [h336] at this
       omega)
    | (rw [toNat_add_ofNat (by omega)]; omega)

/-- **`next_scalars`' iterator is total**, from `kept` and `ScalarsIter.Out`'s frame (`TranscriptAtT.frameS`). -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needN : Nat} (hnN : 48 + needN ≤ need) (hns : NextScalarT.specT env p L.nextScalar.idx needN) :
    specT env p i need :=
  Isa.TContract.mono (kept env p i L hp hL hnN hns) (fun _ _ _ _ h => h)
    (fun _ top regs m _ _ ⟨⟨he, hs, _, hn, hP, _⟩, _⟩ ⟨⟨ha, hf, hst', hK, hA⟩, hc⟩ => by
      have hT := hP.1.frameS hK (he.2 ▸ hP.2.1) hf hn (by omega) (out_miss hP).1 (out_miss hP).2
      exact ⟨⟨ha, hf, hst', hT.1, he.2 ▸ hT.2.1, hT.2.2, hA⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Transcript.ScalarsIterT

/-- info: 'Rv64mc.Proof.Transcript.ScalarsIterT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.ScalarsIterT.total
