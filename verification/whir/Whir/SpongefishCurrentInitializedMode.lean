import Whir.SpongefishCurrentObservedSessionEntry
import Whir.SpongefishCurrentMixedModeCompiler

/-! Current #607 initialized mixed mode. The complete SessionId derivation and
session/zero32 seed are observed ordinary queries. Their actually returned
session selects the subsequent construction domain. No fixed-domain registry,
success certificate, hidden CV or independently supplied session is assumed.

This is the initialized byte-cursor source adapter, not the native PCS equation
machine, Merkle/original-claim observer, Rust compiler correspondence or a
Fiat-Shamir knowledge endpoint. Empty instance input is outside native
constructor correspondence because Rust panics there. -/
namespace Whir.SpongefishCurrentInitializedMode
open Concrete FiatShamirGame DuplexRefinement DuplexModeGame
open SpongefishSessionAdapter SpongefishPCSRoundFrames SpongefishCurrentModeQueries
set_option autoImplicit false

abbrev Result := Except (SpongefishCurrentMixedModeCompiler.Data ×
  SpongefishCurrentPrimitiveEventCompiler.ReplayError) SpongefishCurrentMixedModeCompiler.Data

/-- Semantic data is reconstructed from the literal constructor input and its
observed derived domain. The ordinary setup's physical CV is intentionally not
an independent construction-oracle state. -/
def initial (session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) : SpongefishCurrentMixedModeCompiler.SemanticCursor where
  data := SpongefishCurrentMixedModeCompiler.forget
    (SpongefishCurrentObservedSessionEntry.cursor session instanceBytes narg hints {cv := zeroDigest})
  framed := bind_frame_domain {domain := session} instanceBytes (initial_frame_domain session)
    (by simp [maxCursor])
  bounded := by
    by_cases empty : instanceBytes = [] <;>
      simp [SpongefishCurrentMixedModeCompiler.forget,SpongefishCurrentObservedSessionEntry.cursor,
        SpongefishPCSRoundFrames.bind,empty,maxCursor]

@[simp] theorem initial_data (session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) (state : State) :
    (initial session instanceBytes narg hints).data =
      SpongefishCurrentMixedModeCompiler.forget
        (SpongefishCurrentObservedSessionEntry.cursor session instanceBytes narg hints state) := rfl

@[simp] theorem constructor_domain (session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) (state : State) :
    (SpongefishCurrentObservedSessionEntry.cursor session instanceBytes narg hints state).pending.domain =
      session := by
  by_cases empty : instanceBytes = [] <;>
    simp [SpongefishCurrentObservedSessionEntry.cursor,SpongefishPCSRoundFrames.bind,empty]

@[simp] theorem initial_weight (session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) :
    SpongefishCurrentMixedModeCompiler.weight (initial session instanceBytes narg hints).data.pending =
      instanceBytes.length+3 := by
  by_cases empty : instanceBytes = [] <;>
    simp [initial,SpongefishCurrentMixedModeCompiler.forget,
      SpongefishCurrentObservedSessionEntry.cursor,SpongefishCurrentMixedModeCompiler.weight,
      SpongefishPCSRoundFrames.bind,retainedBytes,empty]

/-- Setup is the existing observed ordinary program, not a new seed evaluator.
Every callback, including rejecting replay, is in the same shared Program. -/
def program (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (calls : List Call) : Program (Option Result) :=
  WHIRModeFinal.bind
    (SpongefishCurrentObservedSessionEntry.setupProgram parameter tag instanceBytes narg hints)
    (fun result => match result with
      | none => .done none
      | some actual => WHIRModeFinal.bind
          (SpongefishCurrentMixedModeCompiler.replayProgram
            (initial actual.pending.domain instanceBytes narg hints) calls)
          (fun result => .done (some (SpongefishCurrentMixedModeCompiler.eraseResult result))))

def budget (tag instanceBytes : List Byte) (calls : List Call) : Nat :=
  SpongefishCurrentObservedSessionEntry.setupBudget tag instanceBytes +
    SpongefishCurrentMixedModeCompiler.resource (instanceBytes.length+3) calls

theorem program_counted (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (calls : List Call) :
    Counts (budget tag instanceBytes calls) (program parameter tag instanceBytes narg hints calls) := by
  apply WHIRModeFinal.bind_counted _ _
    (SpongefishCurrentObservedSessionEntry.setupBudget tag instanceBytes)
    (SpongefishCurrentMixedModeCompiler.resource (instanceBytes.length+3) calls)
    (SpongefishCurrentObservedSessionEntry.setupProgram_certified parameter tag instanceBytes narg hints).1
  intro result
  cases result with
  | none => trivial
  | some actual =>
    exact SpongefishCurrentPrimitiveEventCompiler.seq_done_counted _ _
      (SpongefishCurrentMixedModeCompiler.replay_counted _ calls _ (by simp))

theorem program_real (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    (runReal C parameter (program parameter tag instanceBytes narg hints calls)).view.result =
      (SpongefishCurrentObservedSessionEntry.actualEntry (compressionOf C) parameter
        tag instanceBytes narg hints calls).map SpongefishCurrentMixedModeCompiler.forgetResult := by
  rw [program,WHIRModeFinal.bind_real_result,SpongefishCurrentObservedSessionEntry.setupProgram_real]
  by_cases empty : instanceBytes = []
  · simp [SpongefishCurrentObservedSessionEntry.actualEntry,
      SpongefishCurrentObservedSessionEntry.actualSetup,newSession,empty,runReal]
  · simp only [SpongefishCurrentObservedSessionEntry.actualSetup,newSession,empty,↓reduceIte,
      Option.map_some,WHIRModeFinal.bind_real_result,runReal]
    have same := SpongefishCurrentMixedModeCompiler.replay_real C parameter
      (initial (derive (compressionOf C) parameter tag) instanceBytes narg hints)
      (SpongefishCurrentObservedSessionEntry.cursor (derive (compressionOf C) parameter tag)
        instanceBytes narg hints
        (absorb (compressionOf C) (init (compressionOf C) parameter
          (derive (compressionOf C) parameter tag)) instanceBytes))
      rfl (session_bridge (compressionOf C) parameter _ instanceBytes)
      (by intro q d found; cases found) calls
    simpa [SpongefishCurrentObservedSessionEntry.actualEntry,
      SpongefishCurrentObservedSessionEntry.actualSetup,newSession,empty] using congrArg some same

/-- The counts apply to every ordinary reply and every construction reply,
including invalid constructor and rejected replay, without an external cap
or a verifier-success premise. -/
theorem program_work (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    (runReal C parameter (program parameter tag instanceBytes narg hints calls)).primitiveCost ≤
      budget tag instanceBytes calls :=
  runReal_counts C parameter _ _ (program_counted parameter tag instanceBytes narg hints calls)

structure Input where
  narg : List Byte
  hints : List (List Byte)

/-- An arbitrary counted attacker interaction may generate the proof and
hints from its own oracle answers. Its observations remain before every
initialized-verifier observation in the unchanged shared interpreter. -/
def afterPrefix (parameter : Digest32) (tag instanceBytes : List Byte)
    (prefixProgram : Program Input) (calls : List Call) : Program (Option Result) :=
  WHIRModeFinal.bind prefixProgram (fun input =>
    program parameter tag instanceBytes input.narg input.hints calls)

theorem afterPrefix_counted (parameter : Digest32) (tag instanceBytes : List Byte)
    (prefixProgram : Program Input) (calls : List Call) (A : Nat)
    (attacker : Counts A prefixProgram) :
    Counts (A+budget tag instanceBytes calls)
      (afterPrefix parameter tag instanceBytes prefixProgram calls) :=
  WHIRModeFinal.bind_counted _ _ A _ attacker
    (fun input => program_counted parameter tag instanceBytes input.narg input.hints calls)

/-- Current initialized byte-source coupling, with arbitrary adaptive
attacker prefix and rejection behavior. This is ideal-compression mode
security; it is not a current PCS acceptance or knowledge theorem. -/
theorem afterPrefix_mode_bound {Coins : Type} [Fintype Coins]
    (parameter : Digest32) (tag instanceBytes : List Byte)
    (prefixProgram : Coins → Program Input) (calls : List Call) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin)) (D : View (Option Result) → Bool) :
    let Q := A+budget tag instanceBytes calls
    letI := DuplexPublicSimulator.seedFintype
    ModeAdv (DuplexPublicSimulator.simulator Q) parameter
      (fun coin => afterPrefix parameter tag instanceBytes (prefixProgram coin) calls)
      (fun coin => afterPrefix_counted parameter tag instanceBytes (prefixProgram coin) calls A
        (attacker coin)) D ≤ min 1 ((2*(Q : ℚ)^2-(Q : ℚ))/2^256) := by
  simpa only [duplexModeLoss_eq] using
    PublicCompressionCouplingActualJoint.actual_modeAdv_le_duplexModeLoss
      (AdvCoins := Coins) (R := Option Result) (A+budget tag instanceBytes calls) parameter
      (fun coin => afterPrefix parameter tag instanceBytes (prefixProgram coin) calls)
      (fun coin => afterPrefix_counted parameter tag instanceBytes (prefixProgram coin) calls A
        (attacker coin)) D

#print axioms program_counted
#print axioms program_real
#print axioms program_work
#print axioms afterPrefix_mode_bound
end Whir.SpongefishCurrentInitializedMode
