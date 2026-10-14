import Whir.PCSBCSCapturedSourceTransport

/-! Executable full-table specialization of the erased captured builder. Its
checked equality permits IO tests to run actual first-mention capture and the
actual reply constructor, without compiling Classical erased-key equality. -/
set_option autoImplicit false
namespace Whir.PCSBCSCapturedSourceExecutable
open Concrete Protocol CausalGame CausalProbability FiatShamirGame
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSMerkleRootCache
open PCSBCSSourceCallerSnapshot PCSBCSSourceReplyInversion
open TypedOracleCompiler TypedFiatShamirGame PCSStateRestoration.Latent
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- Same first-disclosure walk, using the Reference's executable equality. The
key equality instance is not consulted by the disclosure finder. -/
def capture {R : Type} {n : Nat} (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) : Option Frozen :=
  (PCSBCSFirstRootDisclosure.firstMention addresses ref program table).map fun events =>
    freeze (PCSBCSSourceRootCapture.ordinaryPrefix events) ref.root ref.shape

/-- Only references addressed by the current literal packet are enabled. -/
def registry {R : Type} {n : Nat} (addresses : Keys → List Reference)
    (program : Sampling Keys Answers R n) (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) : PCSBCSSourceFrozenAccessor.Captures :=
  fun ref => if ref ∈ addresses (.inl current) then capture addresses ref program table else none

/-- Actual first-mention freezing, strict previous packet tape, and checked
frozen reply decoding. This is not a supplied oracle or a supplied success
certificate. The table's selected answer is never an incoming-state input. -/
def snapshotFromTable {R : Type} {n : Nat} (addresses : Keys → List Reference)
    (ref : Reference) (program : Sampling Keys Answers R n)
    (original : PCSBCSCallerBinding.CallerInput p) (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (table : Table Keys Answers) :
    Option (PCSBCSCallerBinding.CallerData p) := do
  let captures := registry addresses program current table
  let root ← captures ref
  let replies ← PCSBCSSourceFrozenReplies.replies current.2.coord saved captures current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val))
  pure ⟨original,PCSBCSRestorationHazard.incomingData p root.raw
    (PCSBCSSourcePacketTape.ringPrefix current (fun key => table key.val))
    (PCSBCSSourcePacketTape.tape current (fun key => table key.val)) replies current.2.coord⟩

theorem capture_eq {R : Type} {n : Nat} (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) :
    capture addresses ref program table = PCSBCSSourceRootCapture.capture addresses ref program table := by
  unfold capture PCSBCSSourceRootCapture.capture
  congr 2

/-- The executable specialization is exactly the source constructor on a
shared table, rather than an independently specified approximation. -/
theorem snapshotFromTable_eq {R : Type} {n : Nat} (addresses : Keys → List Reference)
    (ref : Reference) (program : Sampling Keys Answers R n)
    (original : PCSBCSCallerBinding.CallerInput p) (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (table : Table Keys Answers) :
    snapshotFromTable addresses ref program original saved current table =
      fromCapture addresses ref program original saved current (fun key => table key.val) := by
  have same : registry addresses program current table =
      capturedRegistry addresses program current (fun key => table key.val) := by
    rw [capturedRegistry_actual]
    funext reference
    unfold registry
    rw [capture_eq]
  unfold snapshotFromTable fromCapture
  rw [same]

open Classical in
theorem snapshotFromTable_current_independent {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference) (program : Sampling Keys Answers R n)
    (original : PCSBCSCallerBinding.CallerInput p) (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (table : Table Keys Answers)
    (full : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth current.2.coord)) → Digest32) :
    snapshotFromTable addresses ref program original saved current
      (Function.update table (.inl current) full) =
        snapshotFromTable addresses ref program original saved current table := by
  rw [snapshotFromTable_eq,snapshotFromTable_eq]
  exact captured_snapshot_answer_independent addresses ref program original saved current table full

theorem snapshotFromTable_original {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference) (program : Sampling Keys Answers R n)
    (original : PCSBCSCallerBinding.CallerInput p) (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (table : Table Keys Answers)
    (data : PCSBCSCallerBinding.CallerData p)
    (assembled : snapshotFromTable addresses ref program original saved current table = some data) :
    data.original = original := by
  rw [snapshotFromTable_eq] at assembled
  exact captured_original_preserved addresses ref program original saved current
    (fun key => table key.val) data assembled

#print axioms capture_eq
#print axioms snapshotFromTable_eq
#print axioms snapshotFromTable_current_independent
#print axioms snapshotFromTable_original
end Whir.PCSBCSCapturedSourceExecutable
