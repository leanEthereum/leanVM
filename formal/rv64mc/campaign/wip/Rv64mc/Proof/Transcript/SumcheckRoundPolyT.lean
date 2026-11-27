/-
  Rv64mc.Proof.Transcript.SumcheckRoundPolyT

  `Transcript::sumcheck_round_poly(count, claim, eq_factor) -> Result<Vec<E>, VerifierError>` is total (`specT`).
-/

import Rv64mc.Proof.Transcript.NextScalarsT
import Rv64mc.Proof.Transcript.GrindCheckT
import Rv64mc.Proof.Transcript.GrindingBitsT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Field.ESumCopiedSafeT
import Rv64mc.Proof.Runtime.ConcatVecET
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Spec.Transcript.SumcheckRoundPoly
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.SumcheckRoundPoly

namespace Rv64mc.Proof.Transcript.SumcheckRoundPolyT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Transcript.SpongeReprT Rv64mc.Proof.Transcript.TranscriptReprT
open Rv64mc.Proof.Transcript.NextScalarsT (Ctx OkVec PostK)
open Rv64mc.Gen.Verifier.Transcript.Transcript.SumcheckRoundPoly (Link tmpl)

/-- The total precondition: `next_scalar`'s (`NextScalarT.PreT`: the transcript (`a1`) `TranscriptAtT` and owned
    with its proof, the result's slot (`a0`) owned, in a window, 8-byte aligned, apart from both), and the
    `Option<E>` (`a5`) in a window and 8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  NextScalarT.PreT env regs m ∧ InWin env (regs .x15) 24 ∧ (regs .x15).toNat % 8 = 0

/-- The total postcondition: `next_scalars`' (`NextScalarsT.PostT`): the transcript `TranscriptAtT` and owned again,
    its proof's address kept, and, unless the slot holds `Err` (the niche `-1`), the slot a vector (`OkVec`). -/
abbrev PostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  NextScalarsT.PostT env regs m r' m'

/-- **The total contract of `Transcript::sumcheck_round_poly`**: `PreT` to `PostT`, writing at most the slot, the
    sponge and the stream offset (`NextScalar.Out`, the partial contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (NextScalar.Out Layouts.ResultVecE.byteSize) (Stop := AbortStop)

/-- What every part keeps of memory: `SavedT.MemOk` with the thirteen saved registers' slots, from `top - 8` (the
    return address) down to `top - 104` (`s11`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (NextScalar.Out Layouts.ResultVecE.byteSize regs m)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64, 18446744073709551528#64, 18446744073709551520#64,
      18446744073709551512#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20, regs .x21, regs .x22, regs .x23, regs .x24,
      regs .x25, regs .x26, regs .x27] m M

/-- The saved slots lie in the `104` bytes below `top`. -/
theorem slots : SlotsIn 104
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64, 18446744073709551528#64, 18446744073709551520#64,
      18446744073709551512#64] :=
  slots_le

/-- What the parts keep: `Mem`, the transcript `TranscriptAtT` and owned, its proof's address. -/
def BaseM (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Mem env ret top regs m M ∧ TranscriptAtT env M (regs .x11) ∧ OwnedT env M top (regs .x11) ∧
    M.getMem (regs .x11 + 328#64) = m.getMem (regs .x11 + 328#64)

/-- The registers every part keeps: the stack pointer, `s0` (the slot), `s1` (the transcript). -/
def BRegs (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551440#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11

/-- The registers at a call of `next_scalars` or `next_scalar` into the frame (`sp + 0x18`): `BRegs`', and the
    arguments `(sp + 0x18, transcript)`. -/
def ARegs (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  BRegs top regs R ∧ R .x10 = top + 18446744073709551464#64 ∧ R .x11 = regs .x11

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- **`BaseM` across a call** from `sp` (`top - 176`) writing at most words of the frame below the slots, the
    transcript's sponge and its stream offset, and leaving the sponge `SpongeT`; every other word of the frame read
    as before. -/
theorem base_call {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState} {out' : Word → Prop}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 176 ≤ top.toNat)
    (hf : env.Frame (top + 18446744073709551440#64) out' M X) (hc : X.code = M.code) (hs : env.Static X)
    (hout : ∀ a, out' a → (top.toNat - 176 ≤ a.toNat ∧ a.toNat + 104 < top.toNat) ∨
      InRange (regs .x11) Layouts.Sponge.byteSize a ∨ a = regs .x11 + BitVec.ofNat 64 Layouts.Transcript.stream_offset)
    (hk : ∀ a : Word, top + 18446744073709551440#64 ≤ a → ¬ out' a → X.getMem a = M.getMem a)
    (hsT : SpongeT env X (regs .x11)) :
    BaseM env ret top regs m X ∧ ∀ a : Word, top.toNat - 176 ≤ a.toNat → ¬ out' a → X.getMem a = M.getMem a := by
  obtain ⟨hM, hT, hO, hP⟩ := hB
  have hlay := env.layout
  have hnM := hM.1.2.1
  have hsp : (top + 18446744073709551440#64).toNat = top.toNat - 176 := by tn
  obtain ⟨_, hwT, hA, _, hQ, _⟩ := id hT
  obtain ⟨⟨hO1, hO2⟩, ⟨hP1, hP2⟩⟩ := id hO
  have ha := hwT.lt
  have hq := hQ.lt
  unfold Apart at hA
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hA hq ha hO1 hO2 hP1 hP2
  have h336 : (regs .x11 + BitVec.ofNat 64 Layouts.Transcript.stream_offset).toNat = (regs .x11).toNat + 336 :=
    toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)
  have hno : ∀ a : Word, ((regs .x11).toNat + 360 ≤ a.toNat ∨ a.toNat < (regs .x11).toNat) →
      (a.toNat < env.heapEnd.toNat ∨ top.toNat ≤ a.toNat + 104) → ¬ out' a := fun a h1 h2 h => by
    rcases hout a h with h | h | h
    · omega
    · unfold InRange at h; simp only [Layouts.Sponge.byteSize] at h; omega
    · have := congrArg BitVec.toNat h; rw [h336] at this; omega
  have hms : ¬ out' (regs .x11 + BitVec.ofNat 64 328) ∧
      ∀ k, (k = 8 ∨ k = 16) → ¬ out' (M.getMem (regs .x11 + 328#64) + BitVec.ofNat 64 k) := by
    refine ⟨fun h => ?_, fun k hk => hno _ ?_ ?_⟩
    · rcases hout _ h with h | h | h
      · rw [toNat_add_ofNat (by omega)] at h; omega
      · unfold InRange at h; rw [toNat_add_ofNat (by omega)] at h; simp only [Layouts.Sponge.byteSize] at h; omega
      · have := congrArg BitVec.toNat h; rw [h336, toNat_add_ofNat (by omega)] at this; omega
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
  have hTT := hT.frameS hsT (hO.mono (by rw [hsp]; omega)) hf hnM (by rw [hsp]; omega) hms.1 hms.2
  have rd : ∀ a : Word, top.toNat - 176 ≤ a.toNat → ¬ out' a → X.getMem a = M.getMem a := fun a h1 h2 =>
    hk a (Tactic.le_of_toNat (by omega)) h2
  refine ⟨⟨hM.call slots (by omega) (by omega) hf hc hs (fun a ha => ?_) (fun a h1 h2 => rd a (by omega)
    (hno a (by omega) (by omega))), hTT.1, OwnedT.of_next hO hf.1 hTT.2.2, hTT.2.2.trans hP⟩, rd⟩
  rcases hout a ha with h | h | h
  · exact Tactic.mw_stack ⟨by omega, by omega⟩
  · exact Tactic.mw_out (Or.inr (Or.inl h))
  · exact Tactic.mw_out (Or.inr (Or.inr h))

/-- **The sponge kept by a call writing no word of it**, the transcript owned by the caller. -/
theorem sponge_keep {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState} {out' : Word → Prop}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 176 ≤ top.toNat)
    (hk : ∀ a : Word, a.toNat < (env.next M).toNat ∨ (top + 18446744073709551440#64).toNat ≤ a.toNat → ¬ out' a →
      X.getMem a = M.getMem a)
    (hout : ∀ a, out' a → top.toNat - 176 ≤ a.toNat ∧ a.toNat + 104 < top.toNat) : SpongeT env X (regs .x11) := by
  obtain ⟨hM, hT, hO, -⟩ := hB
  have hlay := env.layout
  have hnM := hM.1.2.1
  have hsp : (top + 18446744073709551440#64).toNat = top.toNat - 176 := by tn
  have hlT := hT.2.1.lt
  have hO1 := hO.1.1
  simp only [Layouts.Transcript.byteSize] at hO1 hlT
  have e320 : (regs .x11 + 320#64).toNat = (regs .x11).toNat + 320 := toNat_add_ofNat (k := 320) (by omega)
  refine spongeT_of_get hT.1 (hk _ (by omega) fun h => ?_) (hk _ (by omega) fun h => ?_)
  · have := hout _ h; omega
  · have := hout _ h; omega

/-- The transcript's words `TranscriptAtT` reads, and its proof's, owned at the entry, lie below `NEXT` at the
    entry or at or above `top`. -/
theorem tr_words {env : Env} {m M : MachineState} {top T : Word} (hO : OwnedT env m top T)
    (hT : TranscriptAtT env M T) (hP : M.getMem (T + 328#64) = m.getMem (T + 328#64)) :
    ∀ x : Word, (x = T ∨ x = T + 320#64 ∨ x = T + 328#64 ∨ x = M.getMem (T + 328#64) + 8#64 ∨
      x = M.getMem (T + 328#64) + 16#64) → x.toNat + 8 ≤ (env.next m).toNat ∨ top.toNat ≤ x.toNat := by
  intro x hx
  obtain ⟨⟨hO1, hO2⟩, ⟨hP1, hP2⟩⟩ := hO
  have hlT := hT.2.1.lt
  have hq := hT.2.2.2.2.1.lt
  rw [← hP] at hP1 hP2
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hO1 hO2 hP1 hP2 hlT hq
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega

/-- **`BaseM` across a store** at a word below the transcript's and its proof's words or at or above them: into the
    frame below the slots, or into what the function allocated. -/
theorem base_store {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (hB : BaseM env ret top regs m M) (hO : OwnedT env m top (regs .x11))
    (hM' : Mem env ret top regs m (M.setMem a v)) (hn : env.next (M.setMem a v) = env.next M)
    (ha : (env.next m).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ top.toNat) : BaseM env ret top regs m (M.setMem a v) := by
  obtain ⟨-, hT, hO', hP⟩ := hB
  have hw := tr_words hO hT hP
  have hlT := hT.2.1.lt
  have hq := hT.2.2.2.2.1.lt
  simp only [Layouts.Transcript.byteSize, Layouts.Proof.byteSize] at hlT hq
  have rd : ∀ x : Word, (x = regs .x11 ∨ x = regs .x11 + 320#64 ∨ x = regs .x11 + 328#64 ∨
      x = M.getMem (regs .x11 + 328#64) + 8#64 ∨ x = M.getMem (regs .x11 + 328#64) + 16#64) →
      (M.setMem a v).getMem x = M.getMem x := fun x hx =>
    MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by have := hw x hx; omega))
  have r328 := rd _ (.inr (.inr (.inl rfl)))
  refine ⟨hM', hT.of_get (rd _ (.inl rfl)) (rd _ (.inr (.inl rfl))) r328 (rd _ (.inr (.inr (.inr (.inl rfl)))))
    (rd _ (.inr (.inr (.inr (.inr rfl))))), OwnedT.of_next hO' (by rw [hn]) r328, r328.trans hP⟩

/-- **`BaseM` across a store into the frame** below the slots. -/
theorem base_slot {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (hB : BaseM env ret top regs m M) (hO : OwnedT env m top (regs .x11))
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlo : top.toNat - 176 ≤ a.toNat) (hhi : a.toNat + 112 ≤ top.toNat) :
    BaseM env ret top regs m (M.setMem a v) := by
  have hlay := env.layout
  obtain ⟨h1, n1⟩ := hB.1.slot (v := v) slots (F := 176) hlim hlo (by omega)
  exact base_store hB hO h1 n1 ⟨by omega, by omega⟩

/-- **`BaseM` across a store into what the function allocated.** -/
theorem base_fresh {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (hB : BaseM env ret top regs m M) (hO : OwnedT env m top (regs .x11))
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hlo : (env.next m).toNat ≤ a.toNat)
    (hhi : a.toNat + 8 ≤ (env.next M).toNat) :
    BaseM env ret top regs m (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hnM := hB.1.1.2.1
  obtain ⟨h1, n1⟩ := hB.1.fresh (v := v) slots (by omega) hlo hhi
  exact ⟨base_store hB hO h1 n1 ⟨hlo, by omega⟩, n1⟩

/-- A vector's header given by its words: the buffer `BufT`, under `2^63` bytes, the length at most the capacity. -/
def HdrV (env : Env) (M : MachineState) (c q l : Word) : Prop :=
  BufT env M c q 16 ∧ c.toNat * 16 < 2 ^ 63 ∧ l.toNat ≤ c.toNat

/-- The registers at the allocation after `next_scalars`' return (instructions 34 and 89): `BRegs`, and the
    result's header in `s11`, `s5`, `s10` (`HdrV`). -/
def HRegs (env : Env) (top : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) : Prop :=
  BRegs top regs R ∧ HdrV env M (R .x27) (R .x21) (R .x26)

/-- **The header of a vector in the frame at `sp + 0x18`** (`VecT`) read into `HdrV`. -/
theorem hdrV_of_vecT {env : Env} {M : MachineState} {top : Word} (h : VecT env M (top + 18446744073709551464#64) 16) :
    HdrV env M (M.getMem (top + 18446744073709551464#64)) (M.getMem (top + 18446744073709551472#64))
      (M.getMem (top + 18446744073709551480#64)) := by
  obtain ⟨bc, bp, cc, -, cl⟩ := Runtime.SavedT.hdr_at top 18446744073709551464#64 M
  obtain ⟨-, ⟨-, -, h3, h4⟩, h5⟩ := h
  rw [bc, bp] at h3
  rw [bc] at h4
  rw [cc, cl] at h5
  exact ⟨h3, h4, h5⟩

set_option rv_sym.heap true in
/-- `next_scalars(count - 1)` into the frame (instruction 28), then the branch on its tag: `Err` (instruction 132)
    or the allocation (34). -/
theorem a_ns (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN : Nat} (hnN : 176 + needN ≤ need)
    (hns : NextScalarsT.specT env p L.nextScalars.idx needN)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (herr : ∀ R M, BRegs top regs R ∧ R .x10 = 18446744073709551615#64 ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 264, ret, top⟩ :: rest, R, M⟩)
    (hok : ∀ R M, HRegs env top regs R M ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, ARegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 54, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  rv_introT hR
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  rv_symT hp stop [68, 264] with [hL, hlim] using [hns]
  all_goals try (obtain ⟨-, ⟨⟨_, _, _, _⟩, _, _, _, _, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩, -⟩ := hB; assumption)
  all_goals
    obtain ⟨hB1, -⟩ := base_call hB hlim hret1_14 hret1_31 hret1_15 (fun a ha => by
      simp only [NextScalar.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, InRange,
        Layouts.ResultVecE.byteSize] at ha
      have e : (top + 18446744073709551464#64).toNat = top.toNat - 152 := by tn
      rcases ha with h | h | h
      · rw [e] at h; exact .inl ⟨by omega, by omega⟩
      · exact .inr (.inl h)
      · exact .inr (.inr h)) keep1_1 ⟨hret1_16, hret1_17, hret1_18, hret1_19⟩
  · exact herr _ _ ⟨⟨rfl, rfl, rfl⟩, rfl, hB1⟩
  · exact hok _ _ ⟨⟨⟨rfl, rfl, rfl⟩, hdrV_of_vecT (hret1_30 hc)⟩, hB1⟩

set_option rv_sym.heap true in
/-- `next_scalars(count - 2)` into the frame (instruction 79), then the branch on its tag: `Err` (instruction 132)
    or the allocation (89). -/
theorem b_ns (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN : Nat} (hnN : 176 + needN ≤ need)
    (hns : NextScalarsT.specT env p L.nextScalars.idx needN)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (herr : ∀ R M, BRegs top regs R ∧ R .x10 = 18446744073709551615#64 ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 264, ret, top⟩ :: rest, R, M⟩)
    (hok : ∀ R M, HRegs env top regs R M ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 178, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 158, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  rv_introT hR
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  rv_symT hp stop [178, 264] with [hL, hlim] using [hns]
  all_goals try (obtain ⟨-, ⟨⟨_, _, _, _⟩, _, _, _, _, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩, -⟩ := hB; assumption)
  all_goals
    obtain ⟨hB1, -⟩ := base_call hB hlim hret1_14 hret1_31 hret1_15 (fun a ha => by
      simp only [NextScalar.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, InRange,
        Layouts.ResultVecE.byteSize] at ha
      have e : (top + 18446744073709551464#64).toNat = top.toNat - 152 := by tn
      rcases ha with h | h | h
      · rw [e] at h; exact .inl ⟨by omega, by omega⟩
      · exact .inr (.inl h)
      · exact .inr (.inr h)) keep1_1 ⟨hret1_16, hret1_17, hret1_18, hret1_19⟩
  · exact herr _ _ ⟨⟨rfl, rfl, rfl⟩, rfl, hB1⟩
  · exact hok _ _ ⟨⟨⟨rfl, rfl, rfl⟩, hdrV_of_vecT (hret1_30 hc)⟩, hB1⟩

/-- A block of `n` bytes allocated since the entry, in `M`, 8-byte aligned. -/
def Blk (env : Env) (m M : MachineState) (b : Word) (n : Nat) : Prop :=
  (env.next m).toNat ≤ b.toNat ∧ b.toNat + n ≤ (env.next M).toNat ∧ b.toNat % 8 = 0

/-- `E::sum`'s precondition from a header `HdrV`. -/
theorem sum_pre {env : Env} {M X : MachineState} {c q l : Word} (h : HdrV env M c q l)
    (hn : (env.next M).toNat ≤ (env.next X).toNat) (hnx : (env.next X).toNat ≤ env.heapEnd.toNat) :
    l = 0#64 ∨ env.Live X q (16 * l.toNat) ∧ InWin env q (16 * l.toNat) ∧ q.toNat % 8 = 0 := by
  obtain ⟨hb, -, hl⟩ := h
  rcases hb with h0 | ⟨h1, h2, h3⟩
  · exact .inl (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega))
  · unfold Env.Live at h2 ⊢
    exact .inr ⟨by omega, .inl ⟨h1, by omega⟩, h3⟩

set_option rv_sym.heap true in
/-- `alloc(16)` (instruction 34; the panic on a null pointer refuted), `E::sum` over `next_scalars`' result, to
    `E::mul`'s call (48). -/
theorem a_as (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needE : Nat} (hnA : 176 + needA ≤ need) (hnE : 176 + needE ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hes : Field.ESumCopiedSafeT.SafeT env p L.sumCopiedIterE.idx needE)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hnext : ∀ R M, (HRegs env top regs R M ∧ Blk env m M (R .x24) 16) ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 96, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, HRegs env top regs R M ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨⟨hR, hV⟩, hB⟩
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hes' := hes (R .x26)
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  have hge : 268435456 ≤ (env.next M).toNat := by have := hW.next_ge; omega
  rv_introT hR
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  have hnM := hB.1.1.2.1
  have hX := PLift.up (And.intro hV hB)
  clear hV hB
  rv_symT hp stop [96] with [hL, hlim] using [hac, hes']
  · exact absurd (congrArg BitVec.toNat hc) (by simp only [BitVec.toNat_ofNat]; omega)
  · exact sum_pre hX.down.1 hret1_14.1 hret1_14.2.1
  obtain ⟨hV, hB⟩ := hX.down
  have hB1 := (base_call hB hlim hret1_14 hret1_19 hret1_15 (fun _ h => h.elim) (fun a h _ => keep1_1 a h)
    (sponge_keep (out' := fun _ => False) hB hlim (fun a h _ => keep1_2 a h) fun _ h => h.elim)).1
  have hB3 := (base_call hB1 hlim hret3_14 hret3_16 hret3_15 (fun _ h => h.elim) (fun a h _ => keep3_1 a h)
    (sponge_keep (out' := fun _ => False) hB1 hlim (fun a h _ => keep3_2 a h) fun _ h => h.elim)).1
  have h3 := hret3_14.1
  refine hnext _ _ ⟨⟨⟨⟨rfl, rfl, rfl⟩, ?_⟩, ?_⟩, hB3⟩
  · obtain ⟨hb, hc', hl⟩ := hV
    exact ⟨hb.mono (by have := hret1_14.1; omega), hc', hl⟩
  · show Blk env m m3 (r1 .x10) 16
    have := hB.1.1.1
    have := hret1_16
    simp only [BitVec.toNat_ofNat] at hret1_18
    exact ⟨by omega, by omega, hret1_17⟩

/-- The registers at `concat`'s call (instructions 63 and 114): `BRegs`, the arguments `(sp, sp + 0x18)`. -/
def CRegs (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  BRegs top regs R ∧ R .x10 = top + 18446744073709551440#64 ∧ R .x11 = top + 18446744073709551464#64

/-- The two headers `concat` reads, at `sp + 0x18` and `sp + 0x30`, vectors. -/
def Hdrs (env : Env) (top : Word) (M : MachineState) : Prop :=
  VecT env M (top + 18446744073709551464#64) 16 ∧ VecT env M (top + 18446744073709551488#64) 16

/-- **The first coefficient stored into its block** (`alloc(16)`'s): `BaseM` kept, the block a buffer of one
    element, `NEXT` kept. -/
theorem heap2 {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {b v0 v1 : Word}
    (hB : BaseM env ret top regs m M) (hO : OwnedT env m top (regs .x11))
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hge : 268435456 ≤ (env.next m).toNat)
    (hK : Blk env m M b 16) :
    BaseM env ret top regs m ((M.setMem b v0).setMem (b + 8#64) v1) ∧
      BufT env ((M.setMem b v0).setMem (b + 8#64) v1) 1#64 b 16 ∧
      env.next ((M.setMem b v0).setMem (b + 8#64) v1) = env.next M := by
  obtain ⟨k1, k2, k3⟩ := hK
  have e8 : (b + 8#64).toNat = b.toNat + 8 := toNat_add_ofNat (by have := (env.next M).isLt; omega)
  obtain ⟨h1, n1⟩ := base_fresh (a := b) (v := v0) hB hO hlim k1 (by omega)
  obtain ⟨h2, n2⟩ := base_fresh (a := b + 8#64) (v := v1) h1 hO hlim (by rw [e8]; omega) (by rw [n1, e8]; omega)
  refine ⟨h2, .inr ⟨by omega, ?_, k3⟩, n2.trans n1⟩
  unfold Env.Live
  rw [n2, n1]
  simp only [BitVec.toNat_ofNat]
  omega

/-- **The first two coefficients stored into their block** (`alloc(32)`'s): `BaseM` kept, the block a buffer of
    two elements, `NEXT` kept. -/
theorem heap4 {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {b v0 v1 v2 v3 : Word}
    (hB : BaseM env ret top regs m M) (hO : OwnedT env m top (regs .x11))
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hge : 268435456 ≤ (env.next m).toNat)
    (hK : Blk env m M b 32) :
    BaseM env ret top regs m ((((M.setMem b v0).setMem (b + 8#64) v1).setMem (b + 16#64) v2).setMem (b + 24#64) v3) ∧
      BufT env ((((M.setMem b v0).setMem (b + 8#64) v1).setMem (b + 16#64) v2).setMem (b + 24#64) v3) 2#64 b 16 ∧
      env.next ((((M.setMem b v0).setMem (b + 8#64) v1).setMem (b + 16#64) v2).setMem (b + 24#64) v3) =
        env.next M := by
  obtain ⟨k1, k2, k3⟩ := hK
  have hl := (env.next M).isLt
  have e8 : (b + 8#64).toNat = b.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (b + 16#64).toNat = b.toNat + 16 := toNat_add_ofNat (by omega)
  have e24 : (b + 24#64).toNat = b.toNat + 24 := toNat_add_ofNat (by omega)
  obtain ⟨h1, n1⟩ := base_fresh (a := b) (v := v0) hB hO hlim k1 (by omega)
  obtain ⟨h2, n2⟩ := base_fresh (a := b + 8#64) (v := v1) h1 hO hlim (by rw [e8]; omega) (by rw [n1, e8]; omega)
  obtain ⟨h3, n3⟩ := base_fresh (a := b + 16#64) (v := v2) h2 hO hlim (by rw [e16]; omega) (by rw [n2, n1, e16]; omega)
  obtain ⟨h4, n4⟩ := base_fresh (a := b + 24#64) (v := v3) h3 hO hlim (by rw [e24]; omega) (by rw [n3, n2, n1, e24]; omega)
  refine ⟨h4, .inr ⟨by omega, ?_, k3⟩, n4.trans (n3.trans (n2.trans n1))⟩
  unfold Env.Live
  rw [n4, n3, n2, n1]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The six stores of the two headers into the frame: `(k, b, k)` at `sp + 0x18`, `(c, q, l)` at `sp + 0x30`. -/
abbrev HdrStores (M : MachineState) (top k b c q l : Word) : MachineState :=
  (((((M.setMem (top + 18446744073709551464#64) k).setMem (top + 18446744073709551472#64) b).setMem
    (top + 18446744073709551480#64) k).setMem (top + 18446744073709551488#64) c).setMem
    (top + 18446744073709551496#64) q).setMem (top + 18446744073709551504#64) l

/-- **The two headers stored into the frame** keep `BaseM` and are vectors: the first of `k` elements in a buffer
    `BufT`, the second `HdrV`. -/
theorem hdr_stores {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {k b c q l : Word}
    (hB : BaseM env ret top regs m M) (hO : OwnedT env m top (regs .x11))
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (htop : top.toNat ≤ 0xc0000000) (h16 : top.toNat % 16 = 0)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hb : BufT env M k b 16) (hk : k.toNat * 16 < 2 ^ 63)
    (hV : HdrV env M c q l) :
    BaseM env ret top regs m (HdrStores M top k b c q l) ∧ Hdrs env top (HdrStores M top k b c q l) := by
  have hlay := env.layout
  have e : ∀ c : Nat, 2 ^ 64 - 176 ≤ c → c < 2 ^ 64 →
      (top + BitVec.ofNat 64 c).toNat = top.toNat - (2 ^ 64 - c) := fun c h1 h2 => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, ?_⟩
  · refine base_slot (base_slot (base_slot (base_slot (base_slot (base_slot hB hO hlim hnx ?_ ?_) hO hlim hnx ?_ ?_)
      hO hlim hnx ?_ ?_) hO hlim hnx ?_ ?_) hO hlim hnx ?_ ?_) hO hlim hnx ?_ ?_ <;> tn
  have nx : ∀ (X : MachineState) (c v : Nat), 2 ^ 64 - 176 ≤ c → c < 2 ^ 64 →
      env.next (X.setMem (top + BitVec.ofNat 64 c) (BitVec.ofNat 64 v)) = env.next X := fun X c v h1 h2 =>
    Env.next_setMem_stack (by rw [e c h1 h2]; omega)
  have nx' : ∀ (X : MachineState) (c : Nat) (v : Word), 2 ^ 64 - 176 ≤ c → c < 2 ^ 64 →
      env.next (X.setMem (top + BitVec.ofNat 64 c) v) = env.next X := fun X c v h1 h2 =>
    Env.next_setMem_stack (by rw [e c h1 h2]; omega)
  have wA : ∀ c : Nat, 2 ^ 64 - 176 ≤ c → c + 24 ≤ 2 ^ 64 - 104 → c % 8 = 0 →
      InWin env (top + BitVec.ofNat 64 c) 24 ∧ (top + BitVec.ofNat 64 c).toNat % 8 = 0 := fun c h1 h2 h3 => by
    have := e c h1 (by omega)
    exact ⟨.inr ⟨by omega, by omega⟩, by omega⟩
  obtain ⟨w1, a1⟩ := wA 18446744073709551464 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨w2, a2⟩ := wA 18446744073709551488 (by norm_num) (by norm_num) (by norm_num)
  have n3 : env.next (((M.setMem (top + 18446744073709551464#64) k).setMem (top + 18446744073709551472#64) b).setMem
      (top + 18446744073709551480#64) k) = env.next M := by
    rw [nx' _ 18446744073709551480 _ (by norm_num) (by norm_num), nx' _ 18446744073709551472 _ (by norm_num)
      (by norm_num), nx' _ 18446744073709551464 _ (by norm_num) (by norm_num)]
  have n6 : env.next (HdrStores M top k b c q l) = env.next M := by
    rw [HdrStores, nx' _ 18446744073709551504 _ (by norm_num) (by norm_num), nx' _ 18446744073709551496 _
      (by norm_num) (by norm_num), nx' _ 18446744073709551488 _ (by norm_num) (by norm_num), n3]
  have v1 := NextScalarsT.vecT_stores (M := M) w1 a1 hb hk (Nat.le_refl _)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at v1
  obtain ⟨hbV, hcV, hlV⟩ := hV
  have v2 := NextScalarsT.vecT_stores (M := ((M.setMem (top + 18446744073709551464#64) k).setMem
    (top + 18446744073709551472#64) b).setMem (top + 18446744073709551480#64) k) w2 a2
    (hbV.mono (by rw [n3])) hcV hlV
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at v2
  refine ⟨Layout.FormReprT.vecT_keep v1 (by rw [n6, n3]) fun x h1 h2 => ?_, v2⟩
  rw [e 18446744073709551464 (by norm_num) (by norm_num)] at h1 h2
  have n : ∀ c : Nat, 2 ^ 64 - 176 ≤ c → c < 2 ^ 64 → top.toNat - 128 ≤ top.toNat - (2 ^ 64 - c) →
      x ≠ top + BitVec.ofNat 64 c := fun c h1 h2 h3 =>
    Tactic.ne_of_toNat (by rw [e c h1 h2]; omega)
  rw [HdrStores, MachineState.getMem_setMem_ne (n 18446744073709551504 (by norm_num) (by norm_num) (by omega)),
    MachineState.getMem_setMem_ne (n 18446744073709551496 (by norm_num) (by norm_num) (by omega)),
    MachineState.getMem_setMem_ne (n 18446744073709551488 (by norm_num) (by norm_num) (by omega))]

set_option rv_sym.heap true in
/-- `E::mul` (instruction 48), the polynomial's first coefficient into the block, the two headers into the frame,
    to `concat`'s call (63). -/
theorem a_mul (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM : Nat} (hnM : 176 + needM ≤ need) (hmul : Field.EMulT.specT env p L.mul.idx needM)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hC : Ctx env top regs m)
    (hnext : ∀ R M, CRegs top regs R ∧ BaseM env ret top regs m M ∧ Hdrs env top M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 126, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, (HRegs env top regs R M ∧ Blk env m M (R .x24) 16) ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 96, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨⟨⟨hR, hV⟩, hK⟩, hB⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  have hnx := hB.1.1.2.1
  have hge : 268435456 ≤ (env.next m).toNat := hW.next_ge
  have hhe := hW.heapEnd_le
  obtain ⟨hk1, hk2, hk3⟩ := hK
  rv_introT hR
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  have hX := PLift.up (And.intro hV hB)
  clear hV hB
  rv_symT hp stop [126] with [hL, hlim] using [hmul]
  obtain ⟨hV, hB⟩ := hX.down
  have hB1 := (base_call hB hlim hret1_14 hret1_18 hret1_15 (fun _ h => h.elim) (fun a h _ => keep1_1 a h)
    (sponge_keep (out' := fun _ => False) hB hlim (fun a h _ => keep1_2 a h) fun _ h => h.elim)).1
  have hn1 := hret1_14.1
  have hnx0 : (env.next m).toNat ≤ env.heapEnd.toNat := by have := hB.1.1.1; omega
  obtain ⟨hbV, hcV, hlV⟩ := hV
  refine hnext _ _ ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩, ?_⟩
  exact (fun h => hdr_stores h.1 hC.tO hlim hW.top_le h16 hnx0 h.2.1 (by decide)
    ⟨hbV.mono (by rw [h.2.2]; omega), hcV, hlV⟩) (heap2 hB1 hC.tO hlim hge ⟨hk1, by omega, hk3⟩)

set_option rv_sym.heap true in
/-- `concat` of the two headers into the frame (instruction 64), to the join (117). -/
theorem a_cat (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hnC : 176 + needC ≤ need)
    (hcat : Runtime.ConcatVecET.SpecT env p L.concat.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hnext : ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M ∧ VecT env M (top + 18446744073709551440#64) 16 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 234, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, CRegs top regs R ∧ BaseM env ret top regs m M ∧ Hdrs env top M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 126, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB, hH⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  rv_introT hR
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  obtain ⟨hH1, hH2⟩ := hH
  have hX := PLift.up hB
  clear hB
  have e24 : top + 18446744073709551464#64 + 24#64 = top + 18446744073709551488#64 := by rw [BitVec.add_assoc]; rfl
  have l1 := hH1.2.2
  have l2 := hH2.2.2
  simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
    at l1 l2
  rv_symT hp stop [234] with [hL, hlim] using [hcat]
  · exact hX.down.1.1.2.1
  · rw [e24]; exact hH2.2.1.2.2.1
  · rw [e24]; exact hH2.2.1.2.2.2
  have hB := hX.down
  refine hnext _ _ ⟨⟨rfl, rfl, rfl⟩, (base_call hB hlim hret1_14 hret1_24 hret1_15 (fun a ha => by
    simp only [SretVecOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, InRange,
      Layouts.Vec.byteSize] at ha
    have e : (top + 18446744073709551440#64).toNat = top.toNat - 176 := by tn
    rw [e] at ha
    exact .inl ⟨by omega, by omega⟩) keep1_1 (sponge_keep hB hlim keep1_2 fun a ha => by
      simp only [SretVecOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, InRange,
        Layouts.Vec.byteSize] at ha
      have e : (top + 18446744073709551440#64).toNat = top.toNat - 176 := by tn
      rw [e] at ha
      omega)).1, ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩⟩

set_option rv_sym.heap true in
/-- `concat` of the two headers into the frame (instruction 115), to the join (117). -/
theorem b_cat (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hnC : 176 + needC ≤ need)
    (hcat : Runtime.ConcatVecET.SpecT env p L.concat.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hnext : ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M ∧ VecT env M (top + 18446744073709551440#64) 16 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 234, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, CRegs top regs R ∧ BaseM env ret top regs m M ∧ Hdrs env top M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 228, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB, hH⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  rv_introT hR
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  obtain ⟨hH1, hH2⟩ := hH
  have hX := PLift.up hB
  clear hB
  have e24 : top + 18446744073709551464#64 + 24#64 = top + 18446744073709551488#64 := by rw [BitVec.add_assoc]; rfl
  have l1 := hH1.2.2
  have l2 := hH2.2.2
  simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
    at l1 l2
  rv_symT hp stop [234] with [hL, hlim] using [hcat]
  · exact hX.down.1.1.2.1
  · rw [e24]; exact hH2.2.1.2.2.1
  · rw [e24]; exact hH2.2.1.2.2.2
  have hB := hX.down
  refine hnext _ _ ⟨⟨rfl, rfl, rfl⟩, (base_call hB hlim hret1_14 hret1_24 hret1_15 (fun a ha => by
    simp only [SretVecOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, InRange,
      Layouts.Vec.byteSize] at ha
    have e : (top + 18446744073709551440#64).toNat = top.toNat - 176 := by tn
    rw [e] at ha
    exact .inl ⟨by omega, by omega⟩) keep1_1 (sponge_keep hB hlim keep1_2 fun a ha => by
      simp only [SretVecOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, InRange,
        Layouts.Vec.byteSize] at ha
      have e : (top + 18446744073709551440#64).toNat = top.toNat - 176 := by tn
      rw [e] at ha
      omega)).1, ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩⟩

set_option rv_sym.heap true in
/-- `alloc(32)` (instruction 89; the panic on a null pointer refuted), `E::sum` over `next_scalars`' result, the
    polynomial's first two coefficients into the block, the two headers into the frame, to `concat`'s call (114). -/
theorem b_as (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needE : Nat} (hnA : 176 + needA ≤ need) (hnE : 176 + needE ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hes : Field.ESumCopiedSafeT.SafeT env p L.sumCopiedIterE.idx needE)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hC : Ctx env top regs m)
    (hnext : ∀ R M, CRegs top regs R ∧ BaseM env ret top regs m M ∧ Hdrs env top M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 228, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, HRegs env top regs R M ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 178, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨⟨hR, hV⟩, hB⟩
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hes' := hes (R .x26)
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  have hge : 268435456 ≤ (env.next M).toNat := by have := hW.next_ge; omega
  have hge0 : 268435456 ≤ (env.next m).toNat := hW.next_ge
  have hhe := hW.heapEnd_le
  rv_introT hR
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  have hnM := hB.1.1.2.1
  have hX := PLift.up (And.intro hV hB)
  clear hV hB
  rv_symT hp stop [228] with [hL, hlim] using [hac, hes']
  · exact absurd (congrArg BitVec.toNat hc) (by simp only [BitVec.toNat_ofNat]; omega)
  · exact sum_pre hX.down.1 hret1_14.1 hret1_14.2.1
  obtain ⟨hV, hB⟩ := hX.down
  have hB1 := (base_call hB hlim hret1_14 hret1_19 hret1_15 (fun _ h => h.elim) (fun a h _ => keep1_1 a h)
    (sponge_keep (out' := fun _ => False) hB hlim (fun a h _ => keep1_2 a h) fun _ h => h.elim)).1
  have hB3 := (base_call hB1 hlim hret3_14 hret3_16 hret3_15 (fun _ h => h.elim) (fun a h _ => keep3_1 a h)
    (sponge_keep (out' := fun _ => False) hB1 hlim (fun a h _ => keep3_2 a h) fun _ h => h.elim)).1
  have hn3 := hret3_14.1
  have hn1 := hret1_14.1
  have hnx0 : (env.next m).toNat ≤ env.heapEnd.toNat := by have := hB.1.1.1; omega
  have := hB.1.1.1
  have := hret1_16
  simp only [BitVec.toNat_ofNat] at hret1_18
  obtain ⟨hbV, hcV, hlV⟩ := hV
  refine hnext _ _ ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩, ?_⟩
  exact (fun h => hdr_stores h.1 hC.tO hlim hW.top_le h16 hnx0 h.2.1 (by decide)
    ⟨hbV.mono (by rw [h.2.2]; omega), hcV, hlV⟩) (heap4 hB3 hC.tO hlim hge0 ⟨by omega, by omega, hret1_17⟩)

set_option hygiene false in
/-- The goals left by a return after `Err` stored into the slot: its three stores in `Out`, the sponge kept
    (`sret_spongeT`), `OkVec` refuted by the tag. -/
local macro "err_close" : tactic => `(tactic| (
  have hlS := hwS.lt
  have hlT := hC.tT.2.1.lt
  have o : ∀ k : Nat, k < 24 → NextScalar.Out Layouts.ResultVecE.byteSize regs m (regs .x10 + BitVec.ofNat 64 k) :=
    fun k hk => Or.inl ⟨by rw [toNat_add_ofNat (by omega)]; omega, by
      simp only [Layouts.ResultVecE.byteSize]; rw [toNat_add_ofNat (by omega)]; omega⟩
  have n : ∀ k : Nat, k < 24 → regs .x10 + BitVec.ofNat 64 k ≠ env.nextAddr := fun k hk => hwS.ne_next_add hk
  have o0 : NextScalar.Out Layouts.ResultVecE.byteSize regs m (regs .x10) :=
    Or.inl ⟨Nat.le_refl _, by simp only [Layouts.ResultVecE.byteSize]; omega⟩
  have n0 : regs .x10 ≠ env.nextAddr := hwS.ne_next (Nat.le_refl _) (by omega)
  first
  | exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hM_1 o0 n0) (o 8 (by omega)) (n 8 (by omega)))
      (o 16 (by omega)) (n 16 (by omega))
  | exact (NextScalarsT.sret_spongeT hwS hsT hC.apST hlT).2.2.1
  | exact (NextScalarsT.sret_spongeT hwS hsT hC.apST hlT).2.2.2
  | exact fun h => absurd h10 h
  | exact fun h => absurd rfl h))

set_option rv_sym.heap true in
/-- `Err` into the slot from `next_scalars`' result (instruction 132), the return. -/
theorem err132 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out Layouts.ResultVecE.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 176 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, BRegs top regs R ∧ R .x10 = 18446744073709551615#64 ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 264, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, h10, hB⟩
  have hM := hB.1
  have hsT := hB.2.1.1
  have hc0 := hM.2.1
  have hn0 := hM.1.1
  rv_introT hR
  rv_introT hM
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  rv_symT hp with [hlim]
  all_goals err_close

set_option rv_sym.heap true in
/-- `Err` into the slot from `next_scalar`'s result (instruction 74), the return. -/
theorem err74 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out Layouts.ResultVecE.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 176 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 148, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB⟩
  have hM := hB.1
  have hsT := hB.2.1.1
  have hc0 := hM.2.1
  have hn0 := hM.1.1
  rv_introT hR
  rv_introT hM
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  rv_symT hp with [hlim]
  all_goals err_close

set_option rv_sym.heap true in
/-- `Err` into the slot from `grind_check`'s result (instruction 128), the return. -/
theorem err128 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostK env) (NextScalar.Out Layouts.ResultVecE.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 176 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hC : Ctx env top regs m) :
    ∀ R M, BRegs top regs R ∧ R .x12 = 18446744073709551615#64 ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 256, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, h10, hB⟩
  have hM := hB.1
  have hsT := hB.2.1.1
  have hc0 := hM.2.1
  have hn0 := hM.1.1
  rv_introT hR
  rv_introT hM
  have hwS := hC.wS
  have haS := hC.aS
  have hoS := hC.oS
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  rv_symT hp with [hlim]
  all_goals err_close

set_option rv_sym.heap true in
/-- `next_scalar` into the frame (instruction 69), then the branch on its tag: `Err` (instruction 74) or
    `next_scalars(count - 2)` (79). -/
theorem b_n1 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 176 + needS ≤ need)
    (hn1 : NextScalarT.specT env p L.nextScalar.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (herr : ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 148, ret, top⟩ :: rest, R, M⟩)
    (hok : ∀ R M, BRegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 158, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, ARegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 136, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB⟩
  have hc0 := hB.1.2.1
  have hn0 := hB.1.1.1
  have hs0 := hB.1.2.2.1
  rv_introT hR
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  rv_symT hp stop [148, 158] with [hL, hlim] using [hn1]
  all_goals try (obtain ⟨-, ⟨⟨_, _, _, _⟩, _, _, _, _, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩, -⟩ := hB; assumption)
  all_goals
    obtain ⟨hB1, -⟩ := base_call hB hlim hret1_14 hret1_30 hret1_15 (fun a ha => by
      simp only [NextScalar.Out, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, InRange,
        Layouts.ResultE.byteSize] at ha
      have e : (top + 18446744073709551464#64).toNat = top.toNat - 152 := by tn
      rcases ha with h | h | h
      · rw [e] at h; exact .inl ⟨by omega, by omega⟩
      · exact .inr (.inl h)
      · exact .inr (.inr h)) keep1_1 ⟨hret1_16, hret1_17, hret1_18, hret1_19⟩
  · exact hok _ _ ⟨⟨rfl, rfl, rfl⟩, hB1⟩
  · exact herr _ _ ⟨⟨rfl, rfl, rfl⟩, hB1⟩

/-- The registers after the prologue's stores (instruction 14): the stack pointer, the slot, the transcript, the
    `Option<E>`. -/
def PRegs (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551440#64 ∧ R .x10 = regs .x10 ∧ R .x11 = regs .x11 ∧ R .x15 = regs .x15

set_option rv_sym.heap true in
/-- From the prologue's stores (instruction 14) to the first call: `next_scalars(count - 1)` (instruction 28) where
    the `Option<E>` is `Some`, `next_scalar` (instruction 69) where it is `None`. -/
theorem pro_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 176 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hw : InWin env (regs .x15) 24)
    (ha : (regs .x15).toNat % 8 = 0)
    (hA : ∀ R M, ARegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 54, ret, top⟩ :: rest, R, M⟩)
    (hB : ∀ R M, ARegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 136, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, PRegs top regs R ∧ BaseM env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 28, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hB0⟩
  have hc0 := hB0.1.2.1
  have hn0 := hB0.1.1.1
  have hs0 := hB0.1.2.2.1
  rv_introT hR
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  have hX := PLift.up hB0
  clear hB0
  rv_symT hp stop [54, 136] with [hlim]
  · exact hB _ _ ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩, hX.down⟩
  · exact hA _ _ ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩, hX.down⟩

set_option rv_sym.heap true in
/-- **`sumcheck_round_poly` returns `PostK`**: the prologue, then the parts. -/
theorem kept (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need : Nat} (hn : 176 ≤ need) :
    HoldsT env p i need (PreT env) (PostK env) (NextScalar.Out Layouts.ResultVecE.byteSize)
      (Stop := AbortStop) := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 176 ≤ top.toNat)]
  have hC : Ctx env top regs m := hpre_2 ▸ ⟨⟨⟨hpre_6, hpre_7, hpre_8, hpre_9⟩, hpre_10, hpre_11, hpre_12, hpre_13,
    hpre_14⟩, ⟨⟨hpre_15, hpre_16⟩, ⟨hpre_17, hpre_18⟩⟩, hpre_19, hpre_20, ⟨hpre_23, hpre_24⟩, hpre_21, hpre_22⟩
  clear hpre_6 hpre_7 hpre_8 hpre_9 hpre_10 hpre_11 hpre_12 hpre_13 hpre_14 hpre_15 hpre_16 hpre_17 hpre_18 hpre_19
    hpre_20 hpre_21 hpre_22 hpre_23 hpre_24
  have hrest := pro_ok env p i L hp (Q := Q) (rest := rest) hpre_3 hn hpre_27 hpre_28 hpre_25 hpre_26
    (by sorry) (by sorry)
  rv_symT hp stop [28] with [hL, (by omega : env.stackLimit.toNat + 176 ≤ top.toNat)]
  refine hrest _ _ ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  iterate 7 · rv_closeT
  · simp only [Runtime.SavedT.Saved]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq, and_true]
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).1
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.1
  · exact (hC.tT.frameF hC.tO (by rv_closeT) hpre_5 (by omega)).2.2

end Rv64mc.Proof.Transcript.SumcheckRoundPolyT
