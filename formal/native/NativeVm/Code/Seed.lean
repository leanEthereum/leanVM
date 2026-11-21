module

public import NativeVm.Code.Rel
public import NativeVm.Equiv.Verify
public import NativeVm.Transcript.Code

/-!
# The start against the model

`Model.verify` walks from `startState` (`verify_eq_start`): the sponge at `Model.seed`, the cursors
at the starts, no roots. A machine state holding the statement's start (`seedSpecState`: the sponge
at `spongeSeedWith`, the decoded proof's stream and openings, no roots) holds the model's start
(`codeRel_start`), the model's stream and openings being the decoded proof's; so a spec of the
code's `seed` against the statement's start is one against the model's (`seedM_spec`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript NativeVm.Equiv LeanVM.Parameters LeanVM.Semantics
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- The model's start: the sponge at the seed, the cursors at the starts, no roots. -/
def startState (bytecode : Array UInt64) (publicInput : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) : TState :=
  ⟨⟨seed bytecode publicInput, #[], none⟩, stream, 0, openings, 0, #[]⟩

theorem verify_eq_start (bytecode : Array UInt64) (publicInput : Vector UInt64 4)
    (stream : Array EW) (openings : Array (Array OpeningW)) :
    Model.verify bytecode publicInput stream openings =
      match (verifyExecution bytecode publicInput).run (startState bytecode publicInput stream openings)
      with
      | some ((), t) => t.cursor == t.stream.size && t.phase == t.openings.size
      | none => false := (rfl)

/-- The statement's start on the decoded proof `env.proof`. -/
def seedSpecState (env : Env) (bytecode : Array UInt64) (publicInput : Vector UInt64 4) :
    VerifierProgramState :=
  ⟨⟨Id.run (spongeSeedWith (m := Id) keccakF1600 (bytecode.toList.map K.ofLane) publicInput), [], none⟩,
    env.proof.stream, env.proof.openings, []⟩

variable {env : Env} {bytecode : Array UInt64} {publicInput : Vector UInt64 4} {stream : Array EW}
  {openings : Array (Array OpeningW)} {s s' : QState}

/-- **The start**: a state holding the statement's start holds the model's. -/
theorem codeRel_start (hs : SimState env (seedSpecState env bytecode publicInput) s')
    (hstream : stream.toList.map EW.toE = env.proof.stream)
    (hop : openings.toList.map phaseOpenings = env.proof.openings) :
    CodeRel env (startState bytecode publicInput stream openings) s' := by
  refine ⟨seedSpecState env bytecode publicInput, ⟨⟨?_, rfl, rfl⟩, Nat.zero_le _, ?_, Nat.zero_le _, ?_, rfl⟩,
    hs, hstream, hop⟩
  · dsimp only [startState, seedSpecState]
    exact seed_eq bytecode publicInput
  · simpa only [startState, seedSpecState, List.drop_zero] using hstream
  · simpa only [startState, seedSpecState, List.drop_zero] using hop

/-- **`seed`** against the model's start, from a spec of `seed` against the statement's (its frames
`G`, `F` carried through). -/
theorem seedM_spec {G F : QState → Prop}
    (hseed : WP Transcript.seed s (fun s' ↦ SimState env (seedSpecState env bytecode publicInput) s' ∧ G s') F)
    (hstream : stream.toList.map EW.toE = env.proof.stream)
    (hop : openings.toList.map phaseOpenings = env.proof.openings) :
    WP Transcript.seed s
      (fun s' ↦ CodeRel env (startState bytecode publicInput stream openings) s' ∧ G s') F :=
  WP.mono hseed (fun _ ⟨hs, hg⟩ ↦ ⟨codeRel_start hs hstream hop, hg⟩) fun _ h ↦ h

end NativeVm.Code
