/-
  Rv64mc.Spec.Whir.Transcript

  The contracts of the WHIR family's functions that read the transcript, each the mirror's step on the transcript
  state (`Model.TState`, at `a1` as `Spec.Transcript.TranscriptAt` says) with its result written at `sret` (`a0`):
  where the mirror returns a value and `t'`, the slot holds `Ok` with it and the transcript is `t'`; where it fails,
  the slot holds an `Err`. Each writes the slot and the transcript (`TOut`).

  * `read_ood(transcript, vars, bits) -> Result<(Vec<E>, E), VerifierError>` (`lib.rs`; `vars` in `a2`, `bits` in
    `a3`): `Model.readOodRust`, the point a fresh `Vec`;
  * `sample_queries(transcript, block_length, count) -> Result<Vec<u64>, VerifierError>` (`block_length` in `a2`,
    `count` in `a3`): `Model.sampleQueriesRust`, the positions a fresh `Vec`.
-/

import Rv64mc.Spec.Whir.Basic
import Rv64mc.Spec.Multilinear.Basic
import Rv64mc.Model.Whir

namespace Rv64mc.Spec.Whir.Transcript

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript

/-- The transcript at `a1`, the result's slot of `n` bytes at `a0`, both in a caller's frame and apart. -/
def TPre (env : Env) (n : Nat) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  TranscriptAt env m (regs .x11) t ∧ InFrame (regs .x2) (regs .x11) Layouts.Transcript.byteSize ∧
    InFrame (regs .x2) (regs .x10) n ∧ Apart (regs .x10) n (regs .x11) Layouts.Transcript.byteSize

/-- What a transcript reader writes besides its stack and its allocations: the result's slot and the transcript. -/
def TOut (n : Nat) (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) n b ∨ InRange (regs .x11) Layouts.Transcript.byteSize b

/-! ## `read_ood` -/

/-- **The `Result<(Vec<E>, E), VerifierError>` at `a`**: `Ok` with a fresh point and the value, or an `Err`. -/
def OodResultAt (env : Env) (m m' : MachineState) (a : Word) : Option (List E × E) → Prop
  | some (z, v) => m'.getMem (a + BitVec.ofNat 64 Layouts.ResultVecEE.tagOffset) ≠
        BitVec.ofNat 64 Layouts.ResultVecEE.Err.tag ∧
      Spec.Multilinear.FreshVecE env m m' (a + BitVec.ofNat 64 (Layouts.ResultVecEE.Ok.f0 + Layouts.VecEE.f0)) z ∧
      EAt m' (a + BitVec.ofNat 64 (Layouts.ResultVecEE.Ok.f0 + Layouts.VecEE.f1)) (Model.limbs v)
  | none => m'.getMem (a + BitVec.ofNat 64 Layouts.ResultVecEE.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultVecEE.Err.tag

def OodPost (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  match (Model.readOodRust (regs .x12).toNat (regs .x13).toNat).run t with
  | some (r, t') => OodResultAt env m m' (regs .x10) (some r) ∧ TranscriptAt env m' (regs .x11) t'
  | none => OodResultAt env m m' (regs .x10) none

/-- **The contract of `read_ood`**, function `i` of `p` with `need` bytes of stack, for every transcript state. -/
def readOodSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, Holds env p i need (TPre env Layouts.ResultVecEE.byteSize t) (OodPost env t) (TOut Layouts.ResultVecEE.byteSize)

/-! ## `sample_queries` -/

/-- **The `Result<Vec<u64>, VerifierError>` at `a`**: `Ok` with fresh positions, or an `Err`. -/
def QueriesResultAt (env : Env) (m m' : MachineState) (a : Word) : Option (List Word) → Prop
  | some qs => FreshVecW env m m' (a + BitVec.ofNat 64 Layouts.ResultVecU64.Ok.f0) qs
  | none => m'.getMem (a + BitVec.ofNat 64 Layouts.ResultVecU64.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultVecU64.Err.tag

def QueriesPost (env : Env) (t : Model.TState) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  match (Model.sampleQueriesRust (regs .x12) (regs .x13).toNat).run t with
  | some (qs, t') => QueriesResultAt env m m' (regs .x10) (some qs) ∧ TranscriptAt env m' (regs .x11) t'
  | none => QueriesResultAt env m m' (regs .x10) none

/-- **The contract of `sample_queries`**, function `i` of `p` with `need` bytes of stack, for every transcript
    state. -/
def sampleQueriesSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ t, Holds env p i need (TPre env Layouts.ResultVecU64.byteSize t) (QueriesPost env t)
    (TOut Layouts.ResultVecU64.byteSize)

end Rv64mc.Spec.Whir.Transcript
