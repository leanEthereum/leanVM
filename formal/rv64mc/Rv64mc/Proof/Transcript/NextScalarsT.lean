/-
  Rv64mc.Proof.Transcript.NextScalarsT

  `Transcript::next_scalars` (`(0..count).map(|_| self.next_scalar()).collect()`) is total (`specT`): from a
  transcript `TranscriptAtT` (`TranscriptReprT`) owned with its proof (`OwnedT`), and a result's slot as
  `next_scalar`'s (`NextScalarT.PreT`), it returns with the transcript `TranscriptAtT` and owned again, its proof's
  address kept, and, unless the slot holds `Err` (its first word the niche `-1`), the slot a vector
  (`VecReprT.VecT`), writing at most the slot, the sponge and the stream offset besides what it allocates, or ends
  the run with `a0 = 2` where the iterator, `alloc`'s failure (`handle_error`) or `Vec::reserve` does. Safety only:
  the partial contract's elements (`NextScalars.lean`) are `next_scalar`'s functional ones.

  Cut into parts: the entry to the iterator's first call (`kept`, `CallInv`), that call to the loop or the exit
  (`first_ok`), the loop (`loop`, `Total.loop` with the items left in the shunt as the measure, `LInv`: the iterator's
  `PostT` gives the start advanced on `Some`), the element's store (`store_ok`, `SInv`), the exit (`fin_ok`, `FinInv`).
  What every part keeps is `Base`; its memory half `BaseM` is carried across each call and store by a lemma
  (`baseM_iter`, `baseM_callF`, `baseM_callS`, `baseM_store`), not by the executor, and the reads of the frame through
  stores by `getMem_setMem_off` and `rd_heap2`.

  ## Main definitions

  * `PreT`, `OkVec`, `PostT`, `specT`, `PostK`, `Ctx`, `BaseR`, `BaseM`, `Base`, `Shunt`, `Hdr`, `LInv`, `SInv`,
    `FinInv`, `CallInv`

  ## Main results

  * `not_iterOut`, `iter_keep`, `baseM_iter`, `tr_words`, `baseM_store`, `baseM_callF`, `hdr_words`,
    `growOut_hdr`, `vecT_hdr`, `hdr_of_vecT`, `baseM_callS`, `sret_spongeT`, `vecT_stores`, `rd_heap2`, `fin_ok`,
    `store_ok`, `loop`, `first_ok`, `kept`, `total`
-/

import Rv64mc.Proof.Transcript.ScalarsIterT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Spec.Transcript.NextScalars
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.NextScalars

namespace Rv64mc.Proof.Transcript.NextScalarsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Gen.Verifier.Transcript.Transcript.NextScalars (Link tmpl)

/-- The total precondition: `next_scalar`'s (`NextScalarT.PreT`): the transcript `TranscriptAtT` and owned with its
    proof, the result's slot owned, in a window, 8-byte aligned, apart from both. -/
abbrev PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  NextScalarT.PreT env regs m

/-- Unless the slot holds `Err`, the slot a vector of `E`s. -/
def OkVec (env : Env) (regs : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (regs .x10) ≠ 18446744073709551615#64 → VecT env m' (regs .x10) 16

/-- The total postcondition: the transcript `TranscriptAtT` and owned again, its proof's address kept, `OkVec`. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  TranscriptAtT env m' (regs .x11) ∧ OwnedT env m' (regs .x2) (regs .x11) ∧
    m'.getMem (regs .x11 + 328#64) = m.getMem (regs .x11 + 328#64) ∧ OkVec env regs m'

/-- **The total contract of `Transcript::next_scalars`**: `PreT` to `PostT`, writing at most the slot, the sponge
    and the stream offset (`NextScalar.Out`, the partial contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (NextScalar.Out Layouts.ResultVecE.byteSize) (Stop := AbortStop)

/-- What the run gives, from which `PostT` follows with the frame: the sponge `SpongeT`, `OkVec`. -/
def PostK (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x11) ∧ OkVec env regs m'

/-- `PreT`'s facts the parts carry whole, so that the executor's `omega` does not split them. -/
structure Ctx (env : Env) (top : Word) (regs : Reg → Word) (m : MachineState) : Prop where
  tT : TranscriptAtT env m (regs .x11)
  tO : OwnedT env m top (regs .x11)
  wS : InWin env (regs .x10) 24
  aS : (regs .x10).toNat % 8 = 0
  oS : env.Owned m top (regs .x10) 24
  apST : Apart (regs .x10) 24 (regs .x11) Layouts.Transcript.byteSize
  apSP : Apart (regs .x10) 24 (m.getMem (regs .x11 + 328#64)) Layouts.Proof.byteSize

/-- What every part keeps of the registers: the stack pointer, the slot's address, the registers no part writes. -/
def BaseR (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x8 = regs .x10 ∧
    R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27

/-- What every part keeps of the memory: the frame, the code, the static data, the saved registers' slots, the
    transcript `TranscriptAtT` and owned. -/
def BaseM (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (M : MachineState) : Prop :=
  env.Frame top (NextScalar.Out Layouts.ResultVecE.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧
    TranscriptAtT env M (regs .x11) ∧ OwnedT env M top (regs .x11) ∧
    M.getMem (regs .x11 + 328#64) = m.getMem (regs .x11 + 328#64)

/-- What every part keeps: `BaseR` and `BaseM`. -/
def Base (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  BaseR top regs R ∧ BaseM env ret top regs m M

/-- A word of the saved registers' slots, or above the frame, is not one the iterator writes: its slot, the shunt's
    start, the residual are below them, the transcript's sponge and stream offset owned by the caller. -/
theorem not_iterOut {env : Env} {top a : Word} {r : Reg → Word} {M : MachineState} {T : Word}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hnx : (env.next M).toNat ≤ env.heapEnd.toNat)
    (ha : top.toNat - 56 ≤ a.toNat) (ha' : a.toNat < top.toNat)
    (hs : (r .x10).toNat + 24 ≤ top.toNat - 56) (hs' : (r .x11).toNat + 32 ≤ top.toNat - 56)
    (hT : M.getMem (r .x11) = T) (hO : env.Owned M top T Layouts.Transcript.byteSize)
    (hR : M.getMem (r .x11 + 24#64) = top + 18446744073709551432#64) : ¬ ScalarsIter.Out r M a := by
  have hlay := env.layout
  have h184 : (top + 18446744073709551432#64).toNat = top.toNat - 184 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h8 : (r .x11 + 8#64).toNat = (r .x11).toNat + 8 := toNat_add_ofNat (by omega)
  obtain ⟨hO1, hO2⟩ := hO
  simp only [Layouts.Transcript.byteSize] at hO1 hO2
  have h336 : (T + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = T.toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  simp only [ScalarsIter.Out, ScalarsIter.shuntT, ScalarsIter.shuntRes, InRange, hT, hR, h184,
    Layouts.OptionE.byteSize, Layouts.Sponge.byteSize, not_or]
  refine ⟨by omega, fun h => ?_, by omega, fun h => ?_, by omega⟩
  · have := congrArg BitVec.toNat h; rw [h8] at this; omega
  · have := congrArg BitVec.toNat h; rw [h336] at this; omega

/-- **A word of the frame the iterator does not write is kept by it**: not its slot, not the shunt's start, not
    the residual (`sp + 8`), the transcript owned by the caller. -/
theorem iter_keep {env : Env} {top a : Word} {r : Reg → Word} {M m1 : MachineState} {T : Word}
    (hf : env.Frame (top + 18446744073709551424#64) (ScalarsIter.Out r M) M m1)
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hnx : (env.next M).toNat ≤ env.heapEnd.toNat)
    (ha : top.toNat - 192 ≤ a.toNat) (ha' : a.toNat < top.toNat)
    (hs : a.toNat < (r .x10).toNat ∨ (r .x10).toNat + 24 ≤ a.toNat) (h8 : (r .x11 + 8#64).toNat ≠ a.toNat)
    (hr : a.toNat < top.toNat - 184 ∨ top.toNat - 168 ≤ a.toNat)
    (hT : M.getMem (r .x11) = T) (hO : env.Owned M top T Layouts.Transcript.byteSize)
    (hR : M.getMem (r .x11 + 24#64) = top + 18446744073709551432#64) : m1.getMem a = M.getMem a := by
  have hlay := env.layout
  have hsp : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h184 : (top + 18446744073709551432#64).toNat = top.toNat - 184 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨hO1, hO2⟩ := hO
  simp only [Layouts.Transcript.byteSize] at hO1 hO2
  have h336 : (T + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = T.toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  refine hf.getMem_above (by omega) (by rw [hsp]; omega) ?_
  simp only [ScalarsIter.Out, ScalarsIter.shuntT, ScalarsIter.shuntRes, InRange, hT, hR, h184,
    Layouts.OptionE.byteSize, Layouts.Sponge.byteSize, not_or]
  refine ⟨by omega, fun h => h8 (by rw [h]), by omega, fun h => ?_, by omega⟩
  have := congrArg BitVec.toNat h; rw [h336] at this; omega

/-- **`BaseM` across a call of the iterator** from the frame, with its slot and shunt below the saved registers'
    slots, its shunt's transcript the transcript, its residual `sp + 8`. -/
theorem baseM_iter {env : Env} {ret top : Word} {regs r : Reg → Word} {m M m1 : MachineState}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hf : env.Frame (top + 18446744073709551424#64) (ScalarsIter.Out r M) M m1) (hc : m1.code = M.code)
    (hs : env.Static m1) (hT : TranscriptAtT env m1 (regs .x11))
    (hq : m1.getMem (regs .x11 + 328#64) = M.getMem (regs .x11 + 328#64))
    (hx10 : top.toNat - 192 ≤ (r .x10).toNat) (hx10' : (r .x10).toNat + 24 ≤ top.toNat - 56)
    (hx11 : top.toNat - 192 ≤ (r .x11).toNat) (hx11' : (r .x11).toNat + 32 ≤ top.toNat - 56)
    (hsh : M.getMem (r .x11) = regs .x11) (hres : M.getMem (r .x11 + 24#64) = top + 18446744073709551432#64) :
    BaseM env ret top regs m m1 := by
  obtain ⟨hF, hcM, -, h1, h2, h3, h4, h5, h6, h7, -, hO, hP⟩ := hB
  have hlay := env.layout
  have hsp : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hnM : (env.next M).toNat ≤ env.heapEnd.toNat := hF.2.1
  have hkeep : ∀ c : Nat, 0 < c → c ≤ 56 → m1.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) := fun c hc0 hc1 => by
    have e : (top + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = top.toNat - c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact hf.getMem_above (by omega) (by rw [e, hsp]; omega)
      (not_iterOut (by omega) hnM (by rw [e]; omega) (by rw [e]; omega) hx10' hx11' hsh hO.1 hres)
  refine ⟨?_, hc.trans hcM, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT, OwnedT.of_next hO hf.1 hq, hq.trans hP⟩
  · refine Env.Frame.trans hF hf (by omega) fun b hb => ?_
    obtain ⟨hO1, hO2⟩ := hO.1
    simp only [Layouts.Transcript.byteSize] at hO1 hO2
    have h184 : (top + 18446744073709551432#64).toNat = top.toNat - 184 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h8 : (r .x11 + 8#64).toNat = (r .x11).toNat + 8 := toNat_add_ofNat (by omega)
    simp only [ScalarsIter.Out, ScalarsIter.shuntT, ScalarsIter.shuntRes, InRange, hsh, hres, h184,
      Layouts.OptionE.byteSize] at hb
    rcases hb with hb | hb | hb | hb | hb
    · exact Or.inl ⟨by omega, by omega⟩
    · rw [hb]; exact Or.inl ⟨by rw [h8]; omega, by rw [h8]; omega⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb))))
    · exact Or.inl ⟨by omega, by omega⟩
  · exact (hkeep 8 (by omega) (by omega)).trans h1
  · exact (hkeep 16 (by omega) (by omega)).trans h2
  · exact (hkeep 24 (by omega) (by omega)).trans h3
  · exact (hkeep 32 (by omega) (by omega)).trans h4
  · exact (hkeep 40 (by omega) (by omega)).trans h5
  · exact (hkeep 48 (by omega) (by omega)).trans h6
  · exact (hkeep 56 (by omega) (by omega)).trans h7

/-- The transcript's words `TranscriptAtT` reads, and its proof's, owned at entry: below `NEXT` then, or at or
    above the stack top. -/
theorem tr_words {env : Env} {m M : MachineState} {top T : Word} (hO : OwnedT env m top T)
    (hP : M.getMem (T + 328#64) = m.getMem (T + 328#64)) {a : Word} (ha : (env.next m).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ top.toNat) :
    T ≠ a ∧ T + 320#64 ≠ a ∧ T + 328#64 ≠ a ∧ M.getMem (T + 328#64) + 8#64 ≠ a ∧
      M.getMem (T + 328#64) + 16#64 ≠ a := by
  obtain ⟨⟨hT1, hT2⟩, ⟨hP1, hP2⟩⟩ := hO
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hT1 hT2 hP1 hP2
  rw [hP]
  have e320 : (T + 320#64).toNat = T.toNat + 320 := toNat_add_ofNat (by omega)
  have e328 : (T + 328#64).toNat = T.toNat + 328 := toNat_add_ofNat (by omega)
  have e8 : (m.getMem (T + 328#64) + 8#64).toNat = (m.getMem (T + 328#64)).toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (m.getMem (T + 328#64) + 16#64).toNat = (m.getMem (T + 328#64)).toNat + 16 :=
    toNat_add_ofNat (by omega)
  refine ⟨Tactic.ne_of_toNat ?_, Tactic.ne_of_toNat ?_, Tactic.ne_of_toNat ?_, Tactic.ne_of_toNat ?_,
    Tactic.ne_of_toNat ?_⟩ <;>
    (try simp only [e320, e328, e8, e16]) <;> omega

/-- **`BaseM` after a store** to a word not the saved registers' nor the transcript's: in the frame below the
    saved registers' slots, or allocated since the entry. -/
theorem baseM_store {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {a v : Word}
    (hB : BaseM env ret top regs m M) (hO0 : OwnedT env m top (regs .x11))
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (ha : (top.toNat - 192 ≤ a.toNat ∧ a.toNat + 8 ≤ top.toNat - 56) ∨
      ((env.next m).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (env.next M).toNat)) :
    BaseM env ret top regs m (M.setMem a v) := by
  obtain ⟨hF, hcM, hs, h1, h2, h3, h4, h5, h6, h7, hT, hO, hP⟩ := hB
  have hlay := env.layout
  have hnM := hF.2.1
  have hnM' := hF.1
  have hna : a ≠ env.nextAddr := Tactic.ne_of_toNat (by omega)
  have hw := tr_words hO0 hP (a := a) (by omega)
  have hsl : ∀ c : Nat, 0 < c → c ≤ 56 → (M.setMem a v).getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) := fun c hc0 hc1 => by
    have e : (top + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = top.toNat - c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e]; omega))
  have hT' : TranscriptAtT env (M.setMem a v) (regs .x11) :=
    hT.of_get (MachineState.getMem_setMem_ne hw.1) (MachineState.getMem_setMem_ne hw.2.1)
      (MachineState.getMem_setMem_ne hw.2.2.1) (MachineState.getMem_setMem_ne hw.2.2.2.1)
      (MachineState.getMem_setMem_ne hw.2.2.2.2)
  have hq : (M.setMem a v).getMem (regs .x11 + 328#64) = M.getMem (regs .x11 + 328#64) :=
    MachineState.getMem_setMem_ne hw.2.2.1
  refine ⟨?_, by rw [MachineState.code_setMem]; exact hcM, Tactic.static_store hs (by omega), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hT', OwnedT.of_next hO (by rw [Tactic.next_setMem hna]) hq, hq.trans hP⟩
  · rcases ha with ha | ha
    · exact Tactic.frame_slot hF (by omega) (by omega)
    · exact Tactic.frame_fresh hF rfl ha.1 (by omega)
  · exact (hsl 8 (by omega) (by omega)).trans h1
  · exact (hsl 16 (by omega) (by omega)).trans h2
  · exact (hsl 24 (by omega) (by omega)).trans h3
  · exact (hsl 32 (by omega) (by omega)).trans h4
  · exact (hsl 40 (by omega) (by omega)).trans h5
  · exact (hsl 48 (by omega) (by omega)).trans h6
  · exact (hsl 56 (by omega) (by omega)).trans h7

/-- **`BaseM` across a call that writes nothing outside its stack and its allocations**, from a stack top below
    the frame. -/
theorem baseM_callF {env : Env} {ret top top' : Word} {regs : Reg → Word} {m M m1 : MachineState}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat ≤ top'.toNat)
    (htop : top'.toNat + 136 ≤ top.toNat) (hf : env.Frame top' Tactic.F M m1) (hc : m1.code = M.code)
    (hs : env.Static m1) : BaseM env ret top regs m m1 := by
  obtain ⟨hF, hcM, -, h1, h2, h3, h4, h5, h6, h7, hT, hO, hP⟩ := hB
  have hlay := env.layout
  have hnM := hF.2.1
  have hf' : env.Frame top Tactic.F M m1 := Env.Frame.trans (Env.Frame.refl hnM) hf (by omega) fun _ h => h.elim
  have hTT := hT.frameF hO hf' hnM (by omega)
  have hsl : ∀ c : Nat, 0 < c → c ≤ 56 → m1.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) := fun c hc0 hc1 => by
    have e : (top + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = top.toNat - c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact hf.getMem_above (by omega) (by rw [e]; omega) id
  refine ⟨Env.Frame.trans hF hf (by omega) fun _ h => h.elim, hc.trans hcM, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hTT.1,
    hTT.2.1, hTT.2.2.trans hP⟩
  · exact (hsl 8 (by omega) (by omega)).trans h1
  · exact (hsl 16 (by omega) (by omega)).trans h2
  · exact (hsl 24 (by omega) (by omega)).trans h3
  · exact (hsl 32 (by omega) (by omega)).trans h4
  · exact (hsl 40 (by omega) (by omega)).trans h5
  · exact (hsl 48 (by omega) (by omega)).trans h6
  · exact (hsl 56 (by omega) (by omega)).trans h7

/-- The result's three words stored into a slot in a window, apart from the transcript, keep its sponge
    `SpongeT`. -/
theorem sret_spongeT {env : Env} {M : MachineState} {a T v0 v1 v2 : Word} (hw : InWin env a 24)
    (hT : SpongeT env M T) (hap : Apart a 24 T Layouts.Transcript.byteSize) (hlT : T.toNat + 360 < 2 ^ 64) :
    SpongeT env (((M.setMem a v0).setMem (a + 8#64) v1).setMem (a + 16#64) v2) T := by
  have hlt := hw.lt
  unfold Apart at hap
  simp only [Layouts.Transcript.byteSize] at hap
  have e8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (a + 16#64).toNat = a.toNat + 16 := toNat_add_ofNat (by omega)
  have e320 : (T + 320#64).toNat = T.toNat + 320 := toNat_add_ofNat (by omega)
  have n1 : T ≠ a + 16#64 := Tactic.ne_of_toNat (by rw [e16]; omega)
  have n2 : T ≠ a + 8#64 := Tactic.ne_of_toNat (by rw [e8]; omega)
  have n3 : T ≠ a := Tactic.ne_of_toNat (by omega)
  have n4 : T + 320#64 ≠ a + 16#64 := Tactic.ne_of_toNat (by rw [e16, e320]; omega)
  have n5 : T + 320#64 ≠ a + 8#64 := Tactic.ne_of_toNat (by rw [e8, e320]; omega)
  have n6 : T + 320#64 ≠ a := Tactic.ne_of_toNat (by rw [e320]; omega)
  refine spongeT_of_get hT ?_ ?_
  · rw [MachineState.getMem_setMem_ne n1, MachineState.getMem_setMem_ne n2, MachineState.getMem_setMem_ne n3]
  · rw [MachineState.getMem_setMem_ne n4, MachineState.getMem_setMem_ne n5, MachineState.getMem_setMem_ne n6]

/-- **A `Vec` header stored into a slot** in a window, 8-byte aligned, from a buffer `BufT`. -/
theorem vecT_stores {env : Env} {M : MachineState} {a c q l : Word} (hw : InWin env a 24) (ha : a.toNat % 8 = 0)
    (hb : BufT env M c q 16) (hc : c.toNat * 16 < 2 ^ 63) (hl : l.toNat ≤ c.toNat) :
    VecT env (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l) a 16 := by
  have hlt := hw.lt
  have e8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (a + 16#64).toNat = a.toNat + 16 := toNat_add_ofNat (by omega)
  have n1 : a ≠ a + 16#64 := Tactic.ne_of_toNat (by rw [e16]; omega)
  have n2 : a ≠ a + 8#64 := Tactic.ne_of_toNat (by rw [e8]; omega)
  have n3 : a + 8#64 ≠ a + 16#64 := Tactic.ne_of_toNat (by rw [e8, e16]; omega)
  have hna : ∀ x : Word, x.toNat = a.toNat ∨ x.toNat = a.toNat + 8 ∨ x.toNat = a.toNat + 16 → x ≠ env.nextAddr :=
    fun x hx => hw.ne_next (by omega) (by omega)
  have hn : env.next (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l) = env.next M := by
    rw [Tactic.next_setMem (hna _ (by omega)), Tactic.next_setMem (hna _ (by omega)),
      Tactic.next_setMem (hna _ (by omega))]
  have r0 : (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l).getMem (a + BitVec.ofNat 64 0) = c := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, MachineState.getMem_setMem_ne n1,
      MachineState.getMem_setMem_ne n2, MachineState.getMem_setMem_eq]
  have r8 : (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l).getMem (a + BitVec.ofNat 64 8) = q := by
    rw [show BitVec.ofNat 64 8 = 8#64 from rfl, MachineState.getMem_setMem_ne n3, MachineState.getMem_setMem_eq]
  have r16 : (((M.setMem a c).setMem (a + 8#64) q).setMem (a + 16#64) l).getMem (a + BitVec.ofNat 64 16) = l := by
    rw [show BitVec.ofNat 64 16 = 16#64 from rfl, MachineState.getMem_setMem_eq]
  refine ⟨hw, ⟨hw.sub (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega), ha, ?_, ?_⟩, ?_⟩
  · simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, r0, r8]
    exact hb.mono (by rw [hn])
  · simp only [rvCapAt, Layouts.RawVecInner.cap, r0]; exact hc
  · simp only [vecCap, vecLen, Layouts.Vec.cap, Layouts.Vec.len, r0, r16]; exact hl

/-- A word of the stack, read through two stores into the heap. -/
theorem rd_heap2 {env : Env} {M : MachineState} {x b1 b2 v w : Word} (hx : env.stackLimit.toNat ≤ x.toNat)
    (h1 : b1.toNat < env.heapEnd.toNat) (h2 : b2.toNat < env.heapEnd.toNat) :
    ((M.setMem b1 v).setMem b2 w).getMem x = M.getMem x := by
  have := env.layout
  rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)),
    MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))]

/-- The header at `sp + 0x38`'s words, as `rvCapAt`, `rvPtrAt`, `vecCap` and `vecLen` name them. -/
theorem hdr_words (top : Word) :
    rvCapAt (top + 18446744073709551480#64) = top + 18446744073709551480#64 ∧
      rvPtrAt (top + 18446744073709551480#64) = top + 18446744073709551488#64 ∧
      top + 18446744073709551480#64 + BitVec.ofNat 64 Layouts.Vec.cap = top + 18446744073709551480#64 ∧
      top + 18446744073709551480#64 + BitVec.ofNat 64 Layouts.Vec.len = top + 18446744073709551496#64 := by
  simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, Layouts.Vec.cap, Layouts.Vec.len,
    BitVec.add_assoc]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- What `reserve` writes of the header at `sp + 0x38`: its capacity and pointer, bounds of the frame. -/
theorem growOut_hdr {r : Reg → Word} {M : MachineState} {top a : Word} (hlim : 192 ≤ top.toNat)
    (hr : r .x10 = top + 18446744073709551480#64) (h : GrowOut r M a) :
    a.toNat = top.toNat - 136 ∨ a.toNat = top.toNat - 128 := by
  obtain ⟨h1, h2, -, -⟩ := hdr_words top
  simp only [GrowOut, hr, h1, h2] at h
  rcases h with rfl | rfl
  · left; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · right; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- **The header at `sp + 0x38` a vector's**, from its words. -/
theorem vecT_hdr {env : Env} {M : MachineState} {top : Word} (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (htop : top.toNat ≤ 0xc0000000) (hal : top.toNat % 16 = 0)
    (hb : BufT env M (M.getMem (top + 18446744073709551480#64)) (M.getMem (top + 18446744073709551488#64)) 16)
    (hc : (M.getMem (top + 18446744073709551480#64)).toNat * 16 < 2 ^ 63)
    (hl : (M.getMem (top + 18446744073709551496#64)).toNat ≤ (M.getMem (top + 18446744073709551480#64)).toNat) :
    VecT env M (top + 18446744073709551480#64) 16 := by
  have e : (top + 18446744073709551480#64).toNat = top.toNat - 136 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨h1, h2, h3, h4⟩ := hdr_words top
  refine ⟨Or.inr ⟨by rw [e]; omega, by rw [e]; simp only [Layouts.Vec.byteSize]; omega⟩,
    ⟨Or.inr ⟨by rw [e]; omega, by rw [e]; simp only [Layouts.RawVecInner.byteSize]; omega⟩, by rw [e]; omega, ?_, ?_⟩,
    ?_⟩
  · rw [h1, h2]; exact hb
  · rw [h1]; exact hc
  · simp only [vecLen, vecCap, h3, h4]; exact hl

/-- The header at `sp + 0x38`'s words, from its `VecT`. -/
theorem hdr_of_vecT {env : Env} {M : MachineState} {top : Word} (h : VecT env M (top + 18446744073709551480#64) 16) :
    BufT env M (M.getMem (top + 18446744073709551480#64)) (M.getMem (top + 18446744073709551488#64)) 16 ∧
      (M.getMem (top + 18446744073709551480#64)).toNat * 16 < 2 ^ 63 ∧
      (M.getMem (top + 18446744073709551496#64)).toNat ≤ (M.getMem (top + 18446744073709551480#64)).toNat := by
  obtain ⟨-, ⟨-, -, hb, hc⟩, hl⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := hdr_words top
  rw [h1, h2] at hb
  rw [h1] at hc
  simp only [vecLen, vecCap, h3, h4] at hl
  exact ⟨hb, hc, hl⟩

/-- **`BaseM` across a call that writes, besides its stack and its allocations, only words of the frame below the
    saved registers' slots**, from a stack top below the frame. -/
theorem baseM_callS {env : Env} {ret top top' : Word} {regs : Reg → Word} {m M m1 : MachineState}
    {out : Word → Prop} (hB : BaseM env ret top regs m M) (hO0 : OwnedT env m top (regs .x11))
    (hlim : env.stackLimit.toNat ≤ top'.toNat) (hlim2 : env.stackLimit.toNat + 192 ≤ top.toNat)
    (htop : top'.toNat + 136 ≤ top.toNat)
    (hf : env.Frame top' out M m1) (hc : m1.code = M.code) (hs : env.Static m1)
    (hout : ∀ a, out a → top.toNat - 192 ≤ a.toNat ∧ a.toNat + 8 ≤ top.toNat - 56) :
    BaseM env ret top regs m m1 := by
  obtain ⟨hF, hcM, -, h1, h2, h3, h4, h5, h6, h7, hT, hO, hP⟩ := hB
  have hlay := env.layout
  have hnM := hF.2.1
  have hnx : (env.next m).toNat ≤ env.heapEnd.toNat := by have := hF.1; omega
  have hf' : env.Frame top out M m1 := Env.Frame.trans (Env.Frame.refl hnM) hf (by omega) fun a h => Or.inr (Or.inr
    (Or.inr h))
  have hw := fun (a : Word) (h : out a) => tr_words hO0 hP (a := a) (by have := hout a h; omega)
  have hlimT : env.stackLimit.toNat ≤ top.toNat := by omega
  have hTT := hT.frame hO hf' hnM hlimT
    (fun k hk h => by
      rcases hk with rfl | rfl | rfl
      · exact (hw _ h).1 (by simp)
      · exact (hw _ h).2.1 rfl
      · exact (hw _ h).2.2.1 rfl)
    (fun k hk h => by
      rcases hk with rfl | rfl
      · exact (hw _ h).2.2.2.1 (by rw [hP])
      · exact (hw _ h).2.2.2.2 (by rw [hP]))
  have hsl : ∀ c : Nat, 0 < c → c ≤ 56 → m1.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) := fun c hc0 hc1 => by
    have e : (top + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = top.toNat - c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact hf.getMem_above (by omega) (by rw [e]; omega) fun h => by have := hout _ h; omega
  refine ⟨Env.Frame.trans hF hf (by omega) fun a h => Or.inl (by have := hout a h; constructor <;> omega),
    hc.trans hcM, hs,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hTT.1, hTT.2.1, hTT.2.2.trans hP⟩
  · exact (hsl 8 (by omega) (by omega)).trans h1
  · exact (hsl 16 (by omega) (by omega)).trans h2
  · exact (hsl 24 (by omega) (by omega)).trans h3
  · exact (hsl 32 (by omega) (by omega)).trans h4
  · exact (hsl 40 (by omega) (by omega)).trans h5
  · exact (hsl 48 (by omega) (by omega)).trans h6
  · exact (hsl 56 (by omega) (by omega)).trans h7

/-- The shunt at `sp + 0x50` (the copy the loop passes): the transcript, the end `count`, the residual's address,
    and `k` items left. -/
def Shunt (top : Word) (regs : Reg → Word) (M : MachineState) (k : Nat) : Prop :=
  M.getMem (top + 18446744073709551504#64) = regs .x11 ∧ M.getMem (top + 18446744073709551520#64) = regs .x12 ∧
    M.getMem (top + 18446744073709551528#64) = top + 18446744073709551432#64 ∧
    (M.getMem (top + 18446744073709551512#64)).toNat + k = (regs .x12).toNat

/-- The vector being built, its header at `sp + 0x38` (capacity, pointer, length): the pointer in `x9`, the length
    in `x19` (at least one) and stored, its buffer `BufT`, allocated since the entry, of fewer than `2^63` bytes,
    the length within the capacity, `x18` the last element's offset. -/
def Hdr (env : Env) (top : Word) (m : MachineState) (R : Reg → Word) (M : MachineState) : Prop :=
  R .x9 = M.getMem (top + 18446744073709551488#64) ∧ M.getMem (top + 18446744073709551496#64) = R .x19 ∧
    BufT env M (M.getMem (top + 18446744073709551480#64)) (M.getMem (top + 18446744073709551488#64)) 16 ∧
    (M.getMem (top + 18446744073709551480#64)).toNat * 16 < 2 ^ 63 ∧
    (R .x19).toNat ≤ (M.getMem (top + 18446744073709551480#64)).toNat ∧
    (env.next m).toNat ≤ (M.getMem (top + 18446744073709551488#64)).toNat ∧ 1 ≤ (R .x19).toNat ∧
    (R .x18).toNat = 16 * ((R .x19).toNat - 1)

/-- The loop's head (instruction 104), `k` items left: `Base`, `Hdr`, `Shunt`. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ Hdr env top m R M ∧ Shunt top regs M k

/-- The element's store (instruction 92), `k` items left: `LInv` with the length below the capacity. -/
def SInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  LInv env ret top regs m k R M ∧ (R .x19).toNat < (M.getMem (top + 18446744073709551480#64)).toNat

/-- The exit (instruction 146): `Base`, the vector's capacity, pointer and length in `x10`, `x11`, `x19`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ BufT env M (R .x10) (R .x11) 16 ∧ (R .x10).toNat * 16 < 2 ^ 63 ∧
    (R .x19).toNat ≤ (R .x10).toNat

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

set_option hygiene false in
/-- `NEXT` read through stores into the frame and into the buffer. -/
local macro "next_thru" : tactic => `(tactic| (
  repeat (rw [Tactic.next_setMem]; rotate_left; exact Tactic.ne_of_toNat (by
    first | (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) | ((try rw [h8b]); omega)))))

set_option rv_sym.heap true in
/-- From the exit: `Ok` of the vector or the residual's error into the slot, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out Layouts.ResultVecE.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 192 ≤ need) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, FinInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 146, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hBM := hinv.1.2
  have hbuf := hinv.2
  rv_introT hinv
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  rv_symT hp with [(by omega : env.stackLimit.toNat + 192 ≤ top.toNat)]
  all_goals
    have hlS := hwS.lt
    have hlT := hC.tT.2.1.lt
    have hsT : SpongeT env M (regs .x11) := ⟨hinv_19, hinv_20, hinv_21, hinv_22⟩
    have o0 : NextScalar.Out Layouts.ResultVecE.byteSize regs m (regs .x10) :=
      Or.inl ⟨Nat.le_refl _, by simp only [Layouts.ResultVecE.byteSize]; omega⟩
    have o8 : NextScalar.Out Layouts.ResultVecE.byteSize regs m (regs .x10 + 8#64) := Or.inl (by
      simp only [InRange, Layouts.ResultVecE.byteSize]; rw [toNat_add_ofNat (by omega)]; omega)
    have o16 : NextScalar.Out Layouts.ResultVecE.byteSize regs m (regs .x10 + 16#64) := Or.inl (by
      simp only [InRange, Layouts.ResultVecE.byteSize]; rw [toNat_add_ofNat (by omega)]; omega)
    have n0 : regs .x10 ≠ env.nextAddr := hwS.ne_next (Nat.le_refl _) (by omega)
    have n8 : regs .x10 + 8#64 ≠ env.nextAddr := hwS.ne_next_add (o := 8) (by omega)
    have n16 : regs .x10 + 16#64 ≠ env.nextAddr := hwS.ne_next_add (o := 16) (by omega)
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hinv_9 o0 n0) o8 n8) o16 n16
  · exact (sret_spongeT hwS hsT hC.apST hlT).2.2.1
  · exact (sret_spongeT hwS hsT hC.apST hlT).2.2.2
  · intro _; exact vecT_stores hwS haS hinv_33 hinv_34 hinv_35
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hinv_9 o0 n0) o8 n8) o16 n16
  · exact (sret_spongeT hwS hsT hC.apST hlT).2.2.1
  · exact (sret_spongeT hwS hsT hC.apST hlT).2.2.2
  · intro h; exact absurd rfl h

set_option rv_sym.heap true in
/-- The element stored, the length advanced, back to the loop's head. -/
theorem store_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 192 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) {k : Nat}
    (ih : ∀ R M, LInv env ret top regs m k R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 104, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, SInv env ret top regs m k R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 92, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hBM := hinv.1.1.2
  have hnM := hBM.1.2.1
  obtain ⟨-, ⟨-, -, hb, hc16, -, -, hl1, h18⟩, -⟩ := hinv.1
  have hlt := hinv.2
  obtain ⟨hp0, hpl, hpa⟩ := hb.resolve_left (by omega)
  unfold Env.Live at hpl
  have hA : (M.getMem (top + 18446744073709551488#64) + R .x18 + 16#64).toNat =
      (M.getMem (top + 18446744073709551488#64)).toNat + 16 * (R .x19).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, h18, BitVec.toNat_ofNat]; omega
  have hA8 : (M.getMem (top + 18446744073709551488#64) + R .x18 + 24#64).toNat =
      (M.getMem (top + 18446744073709551488#64)).toNat + 16 * (R .x19).toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, h18, BitVec.toNat_ofNat]; omega
  clear hb
  rv_introT hinv
  rv_symT hp stop [104] with [(by omega : env.stackLimit.toNat + 192 ≤ top.toNat)]
  have hlay := env.layout
  have hx19 : (R .x19 + 1#64).toNat = (R .x19).toNat + 1 := toNat_add_ofNat (by omega)
  have hx18 : (R .x18 + 16#64).toNat = (R .x18).toNat + 16 := toNat_add_ofNat (by omega)
  have hb1 : (M.getMem (top + 18446744073709551488#64) + R .x18 + 16#64).toNat < env.heapEnd.toNat := by omega
  have hb2 : (M.getMem (top + 18446744073709551488#64) + R .x18 + 24#64).toNat < env.heapEnd.toNat := by omega
  have hnb1 : M.getMem (top + 18446744073709551488#64) + R .x18 + 16#64 ≠ env.nextAddr :=
    Tactic.ne_of_toNat (by omega)
  have r128 : ((M.setMem (M.getMem (top + 18446744073709551488#64) + R .x18 + 16#64) (R .x20)).setMem
      (M.getMem (top + 18446744073709551488#64) + R .x18 + 24#64) (R .x21)).getMem (top + 18446744073709551488#64) =
      M.getMem (top + 18446744073709551488#64) := rd_heap2 (by tn) hb1 hb2
  have r136 : ((M.setMem (M.getMem (top + 18446744073709551488#64) + R .x18 + 16#64) (R .x20)).setMem
      (M.getMem (top + 18446744073709551488#64) + R .x18 + 24#64) (R .x21)).getMem (top + 18446744073709551480#64) =
      M.getMem (top + 18446744073709551480#64) := rd_heap2 (by tn) hb1 hb2
  have r112 : ((M.setMem (M.getMem (top + 18446744073709551488#64) + R .x18 + 16#64) (R .x20)).setMem
      (M.getMem (top + 18446744073709551488#64) + R .x18 + 24#64) (R .x21)).getMem (top + 18446744073709551504#64) =
      M.getMem (top + 18446744073709551504#64) := rd_heap2 (by tn) hb1 hb2
  have r104 : ((M.setMem (M.getMem (top + 18446744073709551488#64) + R .x18 + 16#64) (R .x20)).setMem
      (M.getMem (top + 18446744073709551488#64) + R .x18 + 24#64) (R .x21)).getMem (top + 18446744073709551512#64) =
      M.getMem (top + 18446744073709551512#64) := rd_heap2 (by tn) hb1 hb2
  have r96 : ((M.setMem (M.getMem (top + 18446744073709551488#64) + R .x18 + 16#64) (R .x20)).setMem
      (M.getMem (top + 18446744073709551488#64) + R .x18 + 24#64) (R .x21)).getMem (top + 18446744073709551520#64) =
      M.getMem (top + 18446744073709551520#64) := rd_heap2 (by tn) hb1 hb2
  have r88 : ((M.setMem (M.getMem (top + 18446744073709551488#64) + R .x18 + 16#64) (R .x20)).setMem
      (M.getMem (top + 18446744073709551488#64) + R .x18 + 24#64) (R .x21)).getMem (top + 18446744073709551528#64) =
      M.getMem (top + 18446744073709551528#64) := rd_heap2 (by tn) hb1 hb2
  refine ih _ _ ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  iterate 8 · rv_closeT
  · repeat (refine baseM_store ?_ hC.tO (by omega) ?_)
    · exact hBM
    all_goals first
      | (left; constructor <;> tn)
      | (right; (try rw [Tactic.next_setMem hnb1]); omega)
  all_goals simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq, Tactic.rf]
  all_goals (try simp only [r128, r136, r112, r104, r96, r88])
  · refine Or.inr ⟨hp0, ?_, hpa⟩
    unfold Env.Live
    next_thru
    omega
  · exact hc16
  · rw [hx19]; omega
  · exact hinv_38
  · rw [hx19]; omega
  · rw [hx18, hx19, h18]; omega
  · exact hinv_41
  · exact hinv_42
  · exact hinv_43
  · exact hinv_44

set_option rv_sym.heap true in
/-- **The loop**, from its head: the iterator's call, then the exit, or the element stored (after `reserve` where
    the vector is full) and back to the head, one item fewer left. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needI needR : Nat} (hnI : 192 + needI ≤ need) (hnR : 192 + needR ≤ need)
    (hsi : ScalarsIterT.specT env p L.next.idx needI)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out Layouts.ResultVecE.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ k R M, LInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 104, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m) fun k R M hI ih => ?_
  have hBM := hI.1.2
  have hH := hI.2.1
  have hS := hI.2.2
  rv_introT hI
  rw [← hI_41] at hI_19 hI_20 hI_21 hI_22 hI_23 hI_24 hI_25
  rw [← hI_41] at hI_26 hI_27 hI_28 hI_29 hI_30 hI_31
  have hnM := hI_9.1
  rv_symT hp stop [112] with [hL, (by omega : env.stackLimit.toNat + 192 ≤ top.toNat)] using [hsi]
  have hlay := env.layout
  have hsp : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by tn
  have hT1 : TranscriptAtT env m1 (regs .x11) :=
    hI_41 ▸ ⟨⟨hret1_16, hret1_17, hret1_18, hret1_19⟩, hret1_20, hret1_21, hret1_22, hret1_23, hret1_24⟩
  have hB1 : BaseM env ret top regs m m1 := baseM_iter hBM (by omega) hret1_14 hret1_31 hret1_15 hT1
    (by rw [← hI_41]; exact hret1_29)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; tn)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; tn)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; tn)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; tn)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; exact hI_41)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [BitVec.add_assoc]; exact hI_43)
  have hOw := hBM.2.2.2.2.2.2.2.2.2.2.2.1
  have hk_ := fun (a : Word) (h1 : top.toNat - 192 ≤ a.toNat) (h2 : a.toNat < top.toNat)
      (h3 : a.toNat < top.toNat - 80 ∨ top.toNat - 56 ≤ a.toNat) (h4 : top.toNat - 104 ≠ a.toNat)
      (h5 : a.toNat < top.toNat - 184 ∨ top.toNat - 168 ≤ a.toNat) =>
    iter_keep (a := a) hret1_14 (by omega) hBM.1.2.1 h1 h2
      (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
          rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
      h5 (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; exact hI_41) hOw.1
      (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [BitVec.add_assoc]
          exact hI_43)
  have e136 := hk_ (top + 18446744073709551480#64) (by tn) (by tn) (by tn) (by tn) (by tn)
  have e128 := hk_ (top + 18446744073709551488#64) (by tn) (by tn) (by tn) (by tn) (by tn)
  have e120 := hk_ (top + 18446744073709551496#64) (by tn) (by tn) (by tn) (by tn) (by tn)
  have e112 := hk_ (top + 18446744073709551504#64) (by tn) (by tn) (by tn) (by tn) (by tn)
  have e96 := hk_ (top + 18446744073709551520#64) (by tn) (by tn) (by tn) (by tn) (by tn)
  have e88 := hk_ (top + 18446744073709551528#64) (by tn) (by tn) (by tn) (by tn) (by tn)
  have hAdv := hret1_30
  rw [BitVec.add_assoc, BitVec.add_assoc, show (18446744073709551504#64 : Word) + 8#64 = 18446744073709551512#64
    from by decide, show (18446744073709551504#64 : Word) + 16#64 = 18446744073709551520#64 from by decide,
    hI_42] at hAdv
  obtain ⟨hx9, hlen, hbuf, hc16, hlc, hnp, hl1, hx18⟩ := hH
  have hV : VecT env m1 (top + 18446744073709551480#64) 16 :=
    vecT_hdr (by omega) hW.top_le hal (by rw [e136, e128]; exact hbuf.mono (by have := hret1_14.1; omega))
      (by rw [e136]; exact hc16) (by rw [e136, e120, hlen]; exact hlc)
  have hnM1 := hret1_14.1
  have hst : ∀ hc1 : m1.getMem (top + 18446744073709551536#64) ≠ 0#64,
      (m1.getMem (top + 18446744073709551512#64)).toNat + (k - 1) = (regs .x12).toNat ∧ 1 ≤ k := fun hc1 => by
    obtain ⟨hlt, heq⟩ := hAdv hc1
    have := hI_44
    rw [heq, toNat_add_ofNat (by omega)]
    omega
  obtain ⟨-, -, -, h4⟩ := hdr_words top
  have hlen1 : (m1.getMem (top + 18446744073709551496#64)).toNat = (R .x19).toNat := by rw [e120, hlen]
  rv_symT hp stop [92, 146] with [hL, (by omega : env.stackLimit.toNat + 192 ≤ top.toNat)] using [hres]
  -- the exit: `None`
  · refine fin_ok env p i L hp hk hstk (by omega) hnx hal hW hC _ _ ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hB1⟩, ?_, ?_, ?_⟩
    iterate 8 · rv_closeT
    all_goals simp only [Tactic.rf]
    · exact (hdr_of_vecT hV).1
    · exact (hdr_of_vecT hV).2.1
    · rw [e136]; exact hlc
  -- the element stored: the vector has room
  · obtain ⟨hs1, hs2⟩ := hst hc_1
    refine store_ok env p i L hp hstk (by omega) hal hW hC (k := k - 1)
      (fun R' M' h => ih (k - 1) R' M' (by omega) h) _ _
      ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hB1⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, hs1⟩⟩, ?_⟩
    iterate 8 · rv_closeT
    all_goals (try simp only [Tactic.rf])
    · exact e128.symm
    · rw [e120, hlen]
    · exact (hdr_of_vecT hV).1
    · exact (hdr_of_vecT hV).2.1
    · rw [e136]; exact hlc
    · rw [e128]; exact hnp
    · exact hl1
    · exact hx18
    · rw [e112, hI_41]
    · rw [e96, hI_42]
    · rw [e88, hI_43]
    · have : (R .x19).toNat ≠ (m1.getMem (top + 18446744073709551480#64)).toNat := fun h =>
        hc (BitVec.eq_of_toNat_eq h)
      rw [e136] at this ⊢
      omega
  -- the element stored after `reserve` grew the vector
  · obtain ⟨hs1, hs2⟩ := hst hc_1
    have hV2 : VecT env m1 (top + 18446744073709551480#64) 16 :=
      ⟨hret1_19, ⟨hret1_20, hret1_21, hret1_22, hret1_23⟩, hret1_24⟩
    obtain ⟨hb2, hc2, hl2⟩ := hdr_of_vecT hV2
    have hlenE : m1.getMem (top + 18446744073709551496#64) = R .x19 := by
      have := hret1_16
      simp only [vecLen, h4] at this
      rw [this, e120, hlen]
    have hcap := congrArg BitVec.toNat hc
    obtain ⟨hG1, hG2, -⟩ := hret1_18 (by
      simp only [vecCap, vecLen, Layouts.Vec.cap, Layouts.Vec.len, BitVec.add_assoc]
      simp only [show (18446744073709551480#64 : Word) + BitVec.ofNat 64 0 = 18446744073709551480#64 from rfl,
        show (18446744073709551480#64 : Word) + BitVec.ofNat 64 16 = 18446744073709551496#64 from rfl, hlen1, ← hcap,
        show (1#64 : Word).toNat = 1 from rfl]
      omega)
    simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, vecLen, Layouts.Vec.len,
      BitVec.add_assoc] at hG1 hG2
    simp only [show (18446744073709551480#64 : Word) + BitVec.ofNat 64 0 = 18446744073709551480#64 from rfl,
      show (18446744073709551480#64 : Word) + BitVec.ofNat 64 8 = 18446744073709551488#64 from rfl,
      show (18446744073709551480#64 : Word) + BitVec.ofNat 64 16 = 18446744073709551496#64 from rfl, hlen1] at hG1 hG2
    have h192 : 192 ≤ top.toNat := by omega
    have hkr := fun (a : Word) (h1 : top.toNat - 120 ≤ a.toNat) (h2 : a.toNat + 56 ≤ top.toNat) =>
      hret1_14.getMem_above (a := a) (by omega) (by rw [hsp]; omega) fun h => by
        have := growOut_hdr h192 (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]) h
        omega
    refine store_ok env p i L hp hstk (by omega) hal hW hC (k := k - 1)
      (fun R' M' h => ih (k - 1) R' M' (by omega) h) _ _
      ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, baseM_callS hB1 hC.tO (by rw [hsp]; omega) (by omega) (by rw [hsp]; omega)
        hret1_14 hret1_25 hret1_15 fun a h => by
          have := growOut_hdr h192 (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]) h
          omega⟩, ⟨?_, hlenE, hb2, hc2, ?_, ?_, hl1, hx18⟩, ⟨?_, ?_, ?_, ?_⟩⟩, ?_⟩
    iterate 8 · rv_closeT
    all_goals (try simp only [Tactic.rf])
    · rw [hlenE] at hl2; exact hl2
    · have := hG2.1; omega
    · rw [hkr _ (by tn) (by tn), e112, hI_41]
    · rw [hkr _ (by tn) (by tn), e96, hI_42]
    · rw [hkr _ (by tn) (by tn), e88, hI_43]
    · rw [hkr _ (by tn) (by tn)]; exact hs1
    · rw [show (1#64 : Word).toNat = 1 from rfl] at hG1; omega

/-- The state before the iterator's first call (instruction 36): `Base`, the registers kept, the residual (`sp + 8`)
    `-1`, the shunt at `sp + 0x18` (the transcript, the range `0..count`, the residual's address). -/
def CallInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ R .x10 = top + 18446744073709551504#64 ∧ R .x11 = top + 18446744073709551448#64 ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧
    M.getMem (top + 18446744073709551432#64) = 18446744073709551615#64 ∧
    M.getMem (top + 18446744073709551448#64) = regs .x11 ∧ M.getMem (top + 18446744073709551456#64) = 0#64 ∧
    M.getMem (top + 18446744073709551464#64) = regs .x12 ∧
    M.getMem (top + 18446744073709551472#64) = top + 18446744073709551432#64

set_option rv_sym.heap true in
/-- The iterator's first call. -/
theorem first_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needI needA needH needR : Nat} (hnI : 192 + needI ≤ need) (hnA : 192 + needA ≤ need)
    (hnH : 192 + needH ≤ need) (hnR : 192 + needR ≤ need) (hsi : ScalarsIterT.specT env p L.next.idx needI)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out Layouts.ResultVecE.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, CallInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 36, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hBM := hinv.1.2
  rv_introT hinv
  rw [← hinv_40] at hinv_19 hinv_20 hinv_21 hinv_22 hinv_23 hinv_24 hinv_25
  rw [← hinv_40] at hinv_26 hinv_27 hinv_28 hinv_29 hinv_30 hinv_31
  have hnM := hinv_9.1
  rv_symT hp stop [40] with [hL, (by omega : env.stackLimit.toNat + 192 ≤ top.toNat)] using [hsi]
  have hlay := env.layout
  have hsp : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hT1 : TranscriptAtT env m1 (regs .x11) :=
    hinv_40 ▸ ⟨⟨hret1_16, hret1_17, hret1_18, hret1_19⟩, hret1_20, hret1_21, hret1_22, hret1_23, hret1_24⟩
  have hB1 : BaseM env ret top regs m m1 := baseM_iter hBM (by omega) hret1_14 hret1_31 hret1_15 hT1
    (by rw [← hinv_40]; exact hret1_29)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; exact hinv_40)
    (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [BitVec.add_assoc]; exact hinv_43)
  have hAdv := hret1_30
  have hF1 := hret1_14
  have hnM1 := hret1_14.1
  rv_symT hp stop [104, 146] with [hL, (by omega : env.stackLimit.toNat + 192 ≤ top.toNat)] using [hac, hhe]
  · refine fin_ok env p i L hp hk hstk (by omega) hnx hal hW hC _ _ ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hB1⟩, ?_, ?_, ?_⟩
    iterate 8 · rv_closeT
    · exact Or.inl (by simp only [Tactic.rf]; rw [hc]; rfl)
    · simp only [Tactic.rf]; rw [hc]; decide
    · simp only [Tactic.rf]; rw [hc]
  · have hB2 : BaseM env ret top regs m m1 :=
      baseM_callF hB1 (by rw [hsp]; omega) (by rw [hsp]; omega) hret1_14 hret1_19 hret1_15
    refine loop env p i L hp hL hnI hnR hsi hres hstop hk hstk hnx hal hW hC ((regs .x12).toNat - 1) _ _
      ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    iterate 8 · rv_closeT
    all_goals
      have hb0 : (env.next m).toNat ≤ (r1 .x10).toNat := by have := hF1.1; omega
      have hb1 : (r1 .x10).toNat + 64 = (env.next m1).toNat := hret1_18
      have hb2 := hret1_14.2.1
      have hbna : r1 .x10 ≠ env.nextAddr := Tactic.ne_of_toNat (by omega)
      have h8b : (r1 .x10 + 8#64).toNat = (r1 .x10).toNat + 8 := toNat_add_ofNat (by omega)
      have hO := hBM.2.2.2.2.2.2.2.2.2.2.2.1
      have hk_ := fun (a : Word) (h1 : top.toNat - 192 ≤ a.toNat) (h2 : a.toNat < top.toNat)
        (h3 : a.toNat < top.toNat - 112 ∨ top.toNat - 88 ≤ a.toNat) (h4 : top.toNat - 160 ≠ a.toNat)
        (h5 : a.toNat < top.toNat - 184 ∨ top.toNat - 168 ≤ a.toNat) =>
        iter_keep (a := a) hF1 (by omega) hBM.1.2.1 h1 h2
          (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
              rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
          (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
              rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
          h5 (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; exact hinv_40) hO.1
          (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [BitVec.add_assoc]
              exact hinv_43)
      have hadv := hAdv hc_1
      rw [BitVec.add_assoc, BitVec.add_assoc, show (18446744073709551448#64 : Word) + 8#64 = 18446744073709551456#64
        from by decide, show (18446744073709551448#64 : Word) + 16#64 = 18446744073709551464#64 from by decide,
        hinv_41, hinv_42] at hadv
      try simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq, Tactic.rf]
    · repeat (refine baseM_store ?_ hC.tO (by omega) ?_)
      · exact hB2
      all_goals first
        | (left; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        | (right; (try rw [Tactic.next_setMem hbna]); (try rw [h8b]); omega)
    · refine Or.inr ⟨by have := hW.next_ge; omega, ?_, hret1_17⟩
      unfold Env.Live
      next_thru
      rw [show (4#64 : Word).toNat = 4 from rfl]; omega
    · decide
    · decide
    · exact hb0
    · decide
    · decide
    · rw [hk_ _ (by tn) (by tn) (by tn) (by tn) (by tn)]; exact hinv_40
    · rw [hk_ _ (by tn) (by tn) (by tn) (by tn) (by tn)]; exact hinv_42
    · rw [hk_ _ (by tn) (by tn) (by tn) (by tn) (by tn)]; exact hinv_43
    · have h0 := hadv.1
      rw [hadv.2, show (0#64 + 1#64 : Word) = 1#64 from by decide, show (1#64 : Word).toNat = 1 from rfl]
      rw [show (0#64 : Word).toNat = 0 from rfl] at h0
      omega

set_option rv_sym.heap true in
/-- **`Transcript::next_scalars` returns `PostK`.** -/
theorem kept (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needI needA needR needH : Nat} (hnI : 192 + needI ≤ need) (hnA : 192 + needA ≤ need)
    (hnR : 192 + needR ≤ need) (hnH : 192 + needH ≤ need)
    (hsi : ScalarsIterT.specT env p L.next.idx needI) (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hhe : Aborts env p L.handleError.idx needH) :
    HoldsT env p i need (PreT env) (PostK env) (NextScalar.Out Layouts.ResultVecE.byteSize)
      (Stop := AbortStop) := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 192 ≤ top.toNat)]
  have hC : Ctx env top regs m := hpre_2 ▸ ⟨⟨⟨hpre_6, hpre_7, hpre_8, hpre_9⟩, hpre_10, hpre_11, hpre_12, hpre_13, hpre_14⟩,
    ⟨⟨hpre_15, hpre_16⟩, ⟨hpre_17, hpre_18⟩⟩, hpre_19, hpre_20, ⟨hpre_23, hpre_24⟩, hpre_21, hpre_22⟩
  clear hpre_6 hpre_7 hpre_8 hpre_9 hpre_10 hpre_11 hpre_12 hpre_13 hpre_14 hpre_15 hpre_16 hpre_17 hpre_18 hpre_19
    hpre_20 hpre_21 hpre_22 hpre_23 hpre_24
  rv_symT hp stop [36] with [hL, (by omega : env.stackLimit.toNat + 192 ≤ top.toNat)]
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  refine first_ok env p i L hp hL hnI hnA hnH hnR hsi hres hac hhe hstop hk hpre_3 hpre_5 hpre_25 hpre_26 hC _ _
    ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 8 · rv_closeT
  · iterate 5 (refine baseM_store ?_ hC.tO (by omega) ?_)
    · refine ⟨by rv_closeT, by rv_closeT, by rv_closeT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      iterate 7 simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
      · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).1
      · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.1
      · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.2
    all_goals (left; constructor <;> tn)
  all_goals simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq, Tactic.rf]

/-- **`Transcript::next_scalars` is total**, from `kept` and `NextScalar.Out`'s frame (`TranscriptAtT.frameS`). -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needI needA needR needH : Nat} (hnI : 192 + needI ≤ need) (hnA : 192 + needA ≤ need)
    (hnR : 192 + needR ≤ need) (hnH : 192 + needH ≤ need)
    (hsi : ScalarsIterT.specT env p L.next.idx needI) (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hhe : Aborts env p L.handleError.idx needH) : specT env p i need :=
  Isa.TContract.mono (kept env p i L hp hL hnI hnA hnR hnH hsi hal hres hhe) (fun _ _ _ _ h => h)
    (fun _ top regs m _ _ ⟨⟨he, hs, _, hn, hP, _⟩, _⟩ ⟨⟨ha, hf, hst', hK, hV⟩, hc⟩ => by
      have hT := hP.1.1.frameS hK (he.2 ▸ hP.1.2.1) hf hn (by omega) (NextScalarT.out_miss hP.1).1
        (NextScalarT.out_miss hP.1).2
      exact ⟨⟨ha, hf, hst', hT.1, he.2 ▸ hT.2.1, hT.2.2, hV⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Transcript.NextScalarsT

/-- info: 'Rv64mc.Proof.Transcript.NextScalarsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.NextScalarsT.total
