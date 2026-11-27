/-
  Rv64mc.Proof.Transcript.SamplesT

  `Transcript::samples` (`(0..count).map(|_| self.sample()).collect()`) is total (`specT`): into a slot its caller
  owns, from a transcript whose sponge is `SpongeT` and owned, it returns with the slot a vector (`VecReprT.VecT`)
  of `count` elements and the sponge `SpongeT` again, writing at most the slot and the sponge besides what it
  allocates, or ends the run with `a0 = 2` where `handle_error`, `alloc` or `Sponge::sample` does. Safety only: the
  partial contract's elements (`Samples.lean`) are `sample`'s challenges, from `duplex`'s permuted lanes.

  The shape is `FromElemT`'s: the byte count checked, the buffer allocated (the dangling pointer `8` for none), the
  header built in the frame at `sp + 8`, `Vec::reserve` for `count` (which keeps it: the capacity is `count`), the
  loop storing each sample, the header copied to the slot. `rv_autoT` steps to `reserve`'s return (instruction 40),
  `tail_ok` the branch on `count`, `loop` (`Total.loop`, the samples left as the measure) a pass up to the sample,
  `after_ok` its stores and the back edge, `fin_ok` the copy and the return.

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `FinInv`, `LInv`, `LoopCtx`, `TailInv`

  ## Main results

  * `fin_ok`, `cnt_dec`, `after_ok`, `loop`, `hdr_eq`, `tail_ok`, `total`
-/

import Rv64mc.Proof.Transcript.SampleT
import Rv64mc.Proof.Transcript.TranscriptReprT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Proof.Multilinear.SelectorPoint
import Rv64mc.Spec.Transcript.Samples
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.Samples

namespace Rv64mc.Proof.Transcript.SamplesT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Gen.Verifier.Transcript.Transcript.Samples (Link tmpl)

/-- The total precondition: the slot owned, in a window and 8-byte aligned; the transcript's sponge `SpongeT` and
    owned, apart from the slot. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧
    (regs .x10).toNat % 8 = 0 ∧ SpongeT env m (regs .x11) ∧
    env.Owned m (regs .x2) (regs .x11) Layouts.Sponge.byteSize ∧
    Apart (regs .x10) Layouts.Vec.byteSize (regs .x11) Layouts.Sponge.byteSize

/-- The total postcondition: the slot a vector of `count` elements, the sponge `SpongeT`. -/
def PostT (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ vecLen m' (regs .x10) = regs .x12 ∧ SpongeT env m' (regs .x11)

/-- **The total contract of `Transcript::samples`**: `PreT` to `PostT`, writing at most the slot, the sponge and
    the stream offset (`NextScalar.Out`, the partial contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (NextScalar.Out Layouts.Vec.byteSize) (Stop := AbortStop)

/-- The state at the copy of the header to the slot (instruction 55): the registers, the frame, the code, the static
    data, the saved registers' slots, the header's capacity `c` and pointer `q`, the sponge `SpongeT` and owned. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (c q : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x9 = regs .x10 ∧ R .x19 = regs .x12 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top (NextScalar.Out Layouts.Vec.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551544#64) = c ∧ M.getMem (top + 18446744073709551552#64) = q ∧
    SpongeT env M (regs .x11)

set_option rv_sym.heap true in
/-- From the copy of the header: the slot written, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (NextScalar.Out Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn80 : 80 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hw : InWin env (regs .x10) 24) (ha8 : (regs .x10).toNat % 8 = 0)
    (hos : env.Owned m top (regs .x10) 24) (hap : Apart (regs .x10) 24 (regs .x11) 328)
    {c q : Word} (hc : c = regs .x12) (hov : 16 * (regs .x12).toNat < 2 ^ 63) :
    ∀ R M, FinInv env ret top regs m c q R M → BufT env M c q 16 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 110, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv hbM
  have hlt := hw.lt
  have := hW.top_le
  have hown := hos.1
  have o0 : NextScalar.Out Layouts.Vec.byteSize regs m (regs .x10) := Or.inl ⟨Nat.le_refl _, by
    simp only [Layouts.Vec.byteSize]; omega⟩
  have o8 : NextScalar.Out Layouts.Vec.byteSize regs m (regs .x10 + 8#64) := Or.inl ⟨by
    rw [toNat_add_ofNat (by omega)]; omega, by
    rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega⟩
  have o16 : NextScalar.Out Layouts.Vec.byteSize regs m (regs .x10 + 16#64) := Or.inl ⟨by
    rw [toNat_add_ofNat (by omega)]; omega, by
    rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega⟩
  have n0 : regs .x10 ≠ env.nextAddr := hw.ne_next (Nat.le_refl _) (by omega)
  have n8 : regs .x10 + 8#64 ≠ env.nextAddr := hw.ne_next_add (by omega)
  have n16 : regs .x10 + 16#64 ≠ env.nextAddr := hw.ne_next_add (by omega)
  unfold InWin at hw
  unfold Apart at hap
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  · exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hinv_11 o0 n0) o8 n8) o16 n16
  all_goals
    have r0 : ∀ v0 v8 v16 : Word, (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v8).setMem
        (regs .x10 + 16#64) v16).getMem (rvCapAt (regs .x10)) = v0 := fun _ _ _ => by
      simp only [rvCapAt, Layouts.RawVecInner.cap, BitVec.add_zero]
      rw [MachineState.getMem_setMem_ne (Multilinear.SelectorPoint.ne16 _).symm,
        MachineState.getMem_setMem_ne (Multilinear.SelectorPoint.ne8 _).symm, MachineState.getMem_setMem_eq]
    have r8 : ∀ v0 v8 v16 : Word, (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v8).setMem
        (regs .x10 + 16#64) v16).getMem (rvPtrAt (regs .x10)) = v8 := fun _ _ _ => by
      simp only [rvPtrAt, Layouts.RawVecInner.ptr]
      rw [MachineState.getMem_setMem_ne (Multilinear.SelectorPoint.ne8_16 _), MachineState.getMem_setMem_eq]
    rw [r0]
  · rw [r8, hinv_20, hinv_21]
    refine hbM.mono ?_
    rw [Tactic.next_setMem n16, Tactic.next_setMem n8, Tactic.next_setMem n0]
  · rw [hinv_20, hc]; omega

/-- The loop's head (instruction 47) with `k + 1` samples left: the counter, the cursor `x20` past the first half of
    the next element of the block `q`, the frame, the saved slots, the header, the sponge `SpongeT` and owned, the
    block below `NEXT`. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = BitVec.ofNat 64 (k + 1) ∧ R .x9 = regs .x10 ∧
    R .x18 = regs .x11 ∧ R .x19 = regs .x12 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    k + 1 ≤ (regs .x12).toNat ∧ (R .x20).toNat = q.toNat + 16 * ((regs .x12).toNat - (k + 1)) + 8 ∧
    q.toNat + 16 * (regs .x12).toNat ≤ (env.next M).toNat ∧
    env.Frame top (NextScalar.Out Layouts.Vec.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x12 ∧ M.getMem (top + 18446744073709551552#64) = q ∧
    SpongeT env M (regs .x11) ∧ env.Owned m top (regs .x11) Layouts.Sponge.byteSize

theorem cnt_dec (k : Nat) : BitVec.ofNat 64 (k + 1) + 18446744073709551615#64 = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add, BitVec.add_assoc,
    show (BitVec.ofNat 64 1 + 18446744073709551615#64 : Word) = 0#64 from by decide, BitVec.add_zero]

set_option hygiene false in
/-- A word of the frame at or above `sample`'s stack top is kept by it: it writes the sponge, owned by the caller. -/
local macro "slot_keep" : tactic => `(tactic| (
  rw [keep1_1 _ (BitVec.le_def.2 (by simp only [hsp, h8, h16, h24, h32, h40, h48, h64, h72]; omega)) (by
    simp only [Sample.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, Layouts.Sponge.byteSize,
      not_and, Nat.not_lt, h8, h16, h24, h32, h40, h48, h64, h72]
    omega)]))

/-- The hypotheses the loop's parts share. -/
structure LoopCtx (env : Env) (top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) : Prop where
  hstk : env.stackLimit.toNat + 80 ≤ top.toNat
  hal : top.toNat % 16 = 0
  hW : Windows env top m
  hw : InWin env (regs .x10) 24
  ha8 : (regs .x10).toNat % 8 = 0
  hos : env.Owned m top (regs .x10) 24
  hap : Apart (regs .x10) 24 (regs .x11) 328
  hov : 16 * (regs .x12).toNat < 2 ^ 63
  hq0 : (env.next m).toNat ≤ q.toNat
  hq8 : q.toNat % 8 = 0

set_option rv_sym.heap true in
/-- After a sample (instruction 50): its two words stored, the cursor moved; back to the head, or to the copy. -/
theorem after_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn80 : 80 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (NextScalar.Out Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) {q : Word} (hC : LoopCtx env top regs m q) (k : Nat)
    (ih : k ≠ 0 → ∀ R M, LInv env ret top regs m q (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 94, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, LInv env ret top regs m q k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 100, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hstk', hal, hW, hw, ha8, hos, hap, hov, hq0, hq8⟩ := hC
  have hlay := env.layout
  have hge := hW.next_ge
  have := hW.top_le
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk1, hx20, hqn, hF, -, -, -, -, -, -, -, -, -, -, -, hO⟩ := id hI
  have hFn := hF.2.1
  have hnm := hF.1
  have hown := hO.1
  have hx8 : (R .x20 + 18446744073709551608#64).toNat = (R .x20).toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hx16 : (R .x20 + 16#64).toNat = (R .x20).toNat + 16 := toNat_add_ofNat (by have := env.heapEnd.isLt; omega)
  rv_introT hI
  rv_symT hp stop [94, 110] with [(by omega : env.stackLimit.toNat + 80 ≤ top.toNat)]
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (by rw [h0]; decide)
    clear hc
    refine ih hk0 _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hO⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => rw [cnt_dec, Nat.sub_add_cancel (by omega)]
    case refine_13 => omega
    case refine_16 =>
      refine Multilinear.frame_store_heap (Multilinear.frame_store_heap hI_16 ?_ ?_) ?_ ?_
      all_goals
        try rw [Tactic.next_setMem (fun h => by have := congrArg BitVec.toNat h; rw [hx8] at this; omega)]
        try simp only [hx8]
        omega
    all_goals rv_closeT
  · -- the last sample: to the copy
    have hk0 : k = 0 := by
      rw [cnt_dec] at hc
      have := congrArg BitVec.toNat hc
      simp only [BitVec.toNat_ofNat] at this
      omega
    clear hc
    subst hk0
    have hn2 : ∀ (v0 v8 : Word), env.next ((M.setMem (R .x20 + 18446744073709551608#64) v0).setMem (R .x20) v8) =
        env.next M := fun _ _ => by
      rw [Tactic.next_setMem (fun h => by have := congrArg BitVec.toNat h; omega),
        Tactic.next_setMem (fun h => by have := congrArg BitVec.toNat h; rw [hx8] at this; omega)]
    refine fin_ok env p i L hp hk hstk hn80 hal hW hw ha8 hos hap (q := q) rfl hov _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
    all_goals try simp only [Tactic.rf]
    case refine_11 =>
      refine Multilinear.frame_store_heap (Multilinear.frame_store_heap hI_16 ?_ ?_) ?_ ?_
      all_goals
        try rw [Tactic.next_setMem (fun h => by have := congrArg BitVec.toNat h; rw [hx8] at this; omega)]
        try simp only [hx8]
        omega
    case refine_23 =>
      refine Or.inr ⟨by omega, ?_, hq8⟩
      unfold Env.Live
      rw [hn2]
      omega
    all_goals rv_closeT

set_option rv_sym.heap true in
/-- **The loop**, from its head: a sample, then `after_ok`. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 80 + needS ≤ need) (hsa : SampleT.specT env p L.sample.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostT env) (NextScalar.Out Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) {q : Word} (hC : LoopCtx env top regs m q) :
    ∀ k R M, LInv env ret top regs m q k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 94, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m q) fun k R M hI ih => ?_
  have hC' := hC
  obtain ⟨hstk', hal, hW, hw, ha8, hos, hap, hov, hq0, hq8⟩ := hC'
  have hlay := env.layout
  have := hW.top_le
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk1, hx20, hqn, hF, -, -, -, -, -, -, -, -, -, -, -, hO⟩ := id hI
  have hO' : env.Owned M (top + 18446744073709551536#64) (regs .x11) Layouts.Sponge.byteSize :=
    ⟨by have := hO.1; have := hF.1; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega, hO.2⟩
  have hown : (regs .x11).toNat + 328 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x11).toNat := hO.1
  have hnm := hF.1
  have hFn := hF.2.1
  have hsp : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by
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
  have h48 : (top + 18446744073709551568#64).toNat = top.toNat - 48 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rv_introT hI
  rv_symT hp stop [100] with [hL, (by omega : env.stackLimit.toNat + 80 ≤ top.toNat)] using [hsa]
  have hn1 := hret1_14.1
  refine after_ok env p i L hp (by omega) hk hstk hC k (fun hk0 R' M' h => ih (k - 1) R' M' (by omega) h) _ _
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hO⟩
  all_goals try simp only [Tactic.rf]
  case refine_16 =>
    refine Env.Frame.trans hI_16 hret1_14 (by omega) fun b hb => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    simpa only [Sample.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] using hb
  case refine_19 => slot_keep; exact hI_19
  case refine_20 => slot_keep; exact hI_20
  case refine_21 => slot_keep; exact hI_21
  case refine_22 => slot_keep; exact hI_22
  case refine_23 => slot_keep; exact hI_23
  case refine_24 => slot_keep; exact hI_24
  case refine_25 => slot_keep; exact hI_25
  case refine_26 => slot_keep; exact hI_26
  all_goals rv_closeT

/-- The header's words in the frame, as `vecCap`, `vecPtr` and `vecLen` name them. -/
theorem hdr_eq (M : MachineState) (top : Word) :
    vecCap M (top + 18446744073709551544#64) = M.getMem (top + 18446744073709551544#64) ∧
      vecPtr M (top + 18446744073709551544#64) = M.getMem (top + 18446744073709551552#64) ∧
      vecLen M (top + 18446744073709551544#64) = M.getMem (top + 18446744073709551560#64) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [vecCap, vecPtr, vecLen, Layouts.Vec.cap, Layouts.Vec.ptr, Layouts.Vec.len,
    BitVec.add_assoc] <;> rfl

/-- The state at `reserve`'s return (instruction 40): the registers, the frame, the code, the static data, the saved
    registers' slots, the header (capacity `c`, pointer `q`, length `0`), the sponge `SpongeT`. -/
def TailInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (c q : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x18 = regs .x11 ∧
    R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧
    R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top (NextScalar.Out Layouts.Vec.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551544#64) = c ∧ M.getMem (top + 18446744073709551552#64) = q ∧
    M.getMem (top + 18446744073709551560#64) = 0#64 ∧ SpongeT env M (regs .x11)

set_option rv_sym.heap true in
/-- From `reserve`'s return: no sample, straight to the copy; else into the loop. -/
theorem tail_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 80 + needS ≤ need) (hsa : SampleT.specT env p L.sample.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostT env) (NextScalar.Out Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn80 : 80 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hw : InWin env (regs .x10) 24) (ha8 : (regs .x10).toNat % 8 = 0)
    (hos : env.Owned m top (regs .x10) 24) (hap : Apart (regs .x10) 24 (regs .x11) 328)
    (hov : 16 * (regs .x12).toNat < 2 ^ 63) (hO : env.Owned m top (regs .x11) Layouts.Sponge.byteSize) {q : Word} :
    ∀ R M, TailInv env ret top regs m (regs .x12) q R M →
      ((regs .x12).toNat = 0 ∨ ((env.next m).toNat ≤ q.toNat ∧ q.toNat % 8 = 0 ∧
        q.toNat + 16 * (regs .x12).toNat ≤ (env.next M).toNat)) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 80, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hq
  have hge := hW.next_ge
  have hF := hI.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hnm := hF.1
  rv_introT hI
  rv_symT hp stop [94, 110]
  all_goals simp only [hI_24, hI_23]
  · -- no sample
    have h0 : (regs .x12).toNat = 0 := by rw [hc]; rfl
    refine fin_ok env p i L hp hk hstk hn80 hal hW hw ha8 hos hap (q := q) rfl hov _ _ ⟨?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (Or.inl h0)
    all_goals try simp only [Tactic.rf]
    case refine_3 => rw [hc]
    all_goals rv_closeT
  · -- the loop
    have h0 : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hq0, hq8, hq'⟩ := hq.resolve_left h0
    refine loop env p i L hp hL hnS hsa hstop hk hstk ⟨by omega, hal, hW, hw, ha8, hos, hap, hov, hq0, hq8⟩
      ((regs .x12).toNat - 1) _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hO⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => rw [Nat.sub_add_cancel (by omega)]; simp
    case refine_5 => simp
    case refine_13 => omega
    case refine_14 =>
      rw [BitVec.toNat_add, BitVec.toNat_add]
      simp only [BitVec.zero_shiftLeft, BitVec.toNat_ofNat]
      have := env.heapEnd.isLt
      have := hF.2.1
      omega
    all_goals rv_closeT

set_option hygiene false in
/-- `reserve`'s `out` (the header's capacity and pointer) lies in the frame below the stack top. -/
local macro "grow_in" : tactic => `(tactic| (
  simp only [GrowOut, rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, Lprog.updReg_apply,
    Tactic.rf, reduceCtorEq, ↓reduceIte, BitVec.add_zero] at hb
  rcases hb with rfl | rfl
  · exact ⟨by rw [h72]; omega, by rw [h72]; omega⟩
  · rw [BitVec.add_assoc, show (18446744073709551544#64 : Word) + BitVec.ofNat 64 8 = 18446744073709551552#64
      from rfl]
    exact ⟨by rw [h64]; omega, by rw [h64]; omega⟩))

set_option hygiene false in
/-- A saved register's slot, kept by `reserve` (its `out` is the header) and read through the prologue's stores. -/
local macro "slot_r" k:num : tactic => `(tactic| (
  rw [$(Lean.mkIdent (Lean.Name.mkSimple s!"keep{k.getNat}_1")) _
    (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) (by
      simp only [GrowOut, rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, Lprog.updReg_apply,
        Tactic.rf, reduceCtorEq, ↓reduceIte, BitVec.add_zero, BitVec.add_assoc, not_or]
      exact ⟨fun h => absurd ((BitVec.add_right_inj top).1 h) (by decide),
        fun h => absurd ((BitVec.add_right_inj top).1 h) (by decide)⟩)]
  simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]))

set_option rv_sym.heap true in
/-- **`Transcript::samples` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needR needH needS : Nat} (hnA : 80 + needA ≤ need) (hnR : 80 + needR ≤ need)
    (hnH : 80 + needH ≤ need) (hnS : 80 + needS ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hhe : Aborts env p L.handleError.idx needH) (hsa : SampleT.specT env p L.sample.idx needS) :
    specT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [80] with [hL] using [hal', hres, hhe]
  all_goals have hov := Multilinear.SelectorPoint.ovf hc_1
  all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero,
    Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
  all_goals rv_closeT
  all_goals
    have hsp : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · simp only [(hdr_eq _ top).1, (hdr_eq _ top).2.1, (hdr_eq _ top).2.2] at hret1_16 hret1_17
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq] at hret1_16 hret1_17
    have h0 : (regs .x12).toNat = 0 := by have := hov.1; rw [hc] at this; simp at this; omega
    have h17 := hret1_17 (by rw [hc]; simp [h0])
    refine tail_ok env p i L hp hL hnS hsa hstop hk hpre_3 (by omega) hpre_17 hpre_18 hpre_8 hpre_9
      (hpre_2 ▸ ⟨hpre_6, hpre_7⟩) hpre_16 hov.2 (hpre_2 ▸ ⟨hpre_14, hpre_15⟩) (q := 8#64) _ _ ⟨?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (Or.inl h0)
    all_goals try simp only [Tactic.rf]
    all_goals try rv_closeT
    case refine_13 =>
      refine Multilinear.frame_call_own ?_ hret1_14 (by rw [hsp]; omega) fun b hb => ?_
      · rv_closeT
      · grow_in
    case refine_16 => slot_r 1
    case refine_17 => slot_r 1
    case refine_18 => slot_r 1
    case refine_19 => slot_r 1
    case refine_20 => slot_r 1
    case refine_21 => slot_r 1
    have hF1 : env.Frame top Tactic.F m m1 := by
      refine Multilinear.frame_call_own ?_ hret1_14 (by rw [hsp]; omega) fun b hb => ?_
      · rv_closeT
      · grow_in
    have hOs : env.Owned m top (regs .x11) Layouts.Sponge.byteSize := hpre_2 ▸ ⟨hpre_14, hpre_15⟩
    refine spongeT_of_get ⟨hpre_10, hpre_11, hpre_12, hpre_13⟩ ?_ ?_
    · simpa using getMem_owned_out (k := 0) hF1 hpre_5 (by omega) hOs (by decide) id
    · exact getMem_owned_out (k := 320) hF1 hpre_5 (by omega) hOs (by decide) id
  · simp only [(hdr_eq _ top).1, (hdr_eq _ top).2.1, (hdr_eq _ top).2.2] at hret3_16 hret3_17
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq] at hret3_16 hret3_17
    have h17 := hret3_17 (by simp)
    have hF1 : env.Frame top Tactic.F m m3 := by
      refine Multilinear.frame_call_own ?_ hret3_14 (by rw [hsp]; omega) fun b hb => ?_
      · rv_closeT
      · grow_in
    have hOs : env.Owned m top (regs .x11) Layouts.Sponge.byteSize := hpre_2 ▸ ⟨hpre_14, hpre_15⟩
    refine tail_ok env p i L hp hL hnS hsa hstop hk hpre_3 (by omega) hpre_17 hpre_18 hpre_8 hpre_9
      (hpre_2 ▸ ⟨hpre_6, hpre_7⟩) hpre_16 hov.2 hOs (q := r2 .x10) _ _ ⟨?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (Or.inr ⟨?_, ?_, ?_⟩)
    all_goals try simp only [Tactic.rf]
    all_goals try rv_closeT
    case refine_16 =>
      slot_r 3
      rw [keep2_1 _ (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
      simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
    case refine_17 =>
      slot_r 3
      rw [keep2_1 _ (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
      simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
    case refine_18 =>
      slot_r 3
      rw [keep2_1 _ (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
      simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
    case refine_19 =>
      slot_r 3
      rw [keep2_1 _ (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
      simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
    case refine_20 =>
      slot_r 3
      rw [keep2_1 _ (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
      simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
    case refine_21 =>
      slot_r 3
      rw [keep2_1 _ (BitVec.le_def.2 (by rw [hsp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
      simp only [MachineState.getMem_setMem_eq]
    case refine_25 =>
      refine spongeT_of_get ⟨hpre_10, hpre_11, hpre_12, hpre_13⟩ ?_ ?_
      · simpa using getMem_owned_out (k := 0) hF1 hpre_5 (by omega) hOs (by decide) id
      · exact getMem_owned_out (k := 320) hF1 hpre_5 (by omega) hOs (by decide) id

end Rv64mc.Proof.Transcript.SamplesT

/-- info: 'Rv64mc.Proof.Transcript.SamplesT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.SamplesT.total
