import Whir.PCSBCSAdaptiveSourceCallerSnapshot
import Whir.PCSBCSCapturedSourceProbability
import Whir.PCSBCSSourceSavedRecordProvenance

/-! PCS-only adaptive source knowledge relation. Original coordinates may be
earlier caller coins: the actual source decoder and preparation reconstruct
them from erased OTHER values. A single fixed latent model therefore supports
the table average. The native codec/primitive evidence and the separately
charged Merkle bad-event boundary remain explicit; no Rust refinement or
concrete cryptographic assumption is silently added. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSAdaptiveSourceKnowledgeProbability
open Concrete Protocol CausalGame CausalProbability FiatShamirGame
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSSourceCallerSnapshot
open PCSBCSCapturedNativeReplyBridge
open PCSBCSCallerBinding PCSBCSCapturedSourceTransport PCSBCSCapturedSourceAcceptance
open PCSBCSCapturedSourceStatePath PCSBCSRestorationHazard PCSRoundByRoundTranscriptState
open TypedOracleCompiler TypedFiatShamirGame PCSStateRestoration.Latent

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

noncomputable local instance (key : Keys) : Fintype (Answers key) :=
  Restoration.instFintypeAnswer p Q iv boundary key

/-- The original is the exact result of the existing source decoder and
preparation, not a caller held fixed independently of its earlier coins. The
native witness exposes actual acceptance and failure of the actual extractor,
with the fixed primitive and literal full-prefix native codec conditions. -/
structure FailureWitness {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) where
  saved : AnchoredHeaderCodec.Record
  original : CallerInput p
  native : PCSBCSCapturedSourceProbability.FailureWitness layout saved
    (PCSBCSSourceCallerAnswers.answers table) program original table
  constructed : PCSBCSSourceCallerOriginal.original p layout saved native.final.1.val
    (PCSBCSSourceCallerAnswers.answers table) = some original

def Failed {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) : Prop :=
  Nonempty (FailureWitness layout program table)

private theorem path_transport {K : Type} {A : K → Type} {P : Type}
    (old next : NodeModel K A P) (table : Table K A) (exposed : List (Sigma A))
    (sameBefore : ∀ key, (⟨key,table key⟩ : Sigma A) ∈ exposed →
      before next key table = before old key table)
    (sameAfter : ∀ key, (⟨key,table key⟩ : Sigma A) ∈ exposed →
      after next key table = after old key table)
    {start finish : Bool} (path : StatePath old table exposed start finish) :
    StatePath next table exposed start finish := by
  induction path with
  | nil state => exact .nil state
  | step key recorded rest ih =>
    have result : StatePath next table exposed (before next key table) _ :=
      .step key recorded (by simpa only [sameAfter key recorded] using ih)
    simpa only [sameBefore key recorded] using result

private theorem path_exposed_mono {K : Type} {A : K → Type} {P : Type}
    (model : NodeModel K A P) (table : Table K A) (old next : List (Sigma A))
    (subset : ∀ event ∈ old, event ∈ next) {start finish : Bool}
    (path : StatePath model table old start finish) :
    StatePath model table next start finish := by
  induction path with
  | nil state => exact .nil state
  | step key recorded rest ih => exact .step key (subset _ recorded) ih

private theorem data_literal (original : CallerInput p) (root : BaseOracle)
    (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p))
    (replies : Array Reply) (q : Coordinate (ParameterBounds.config p)) (data : CallerData p)
    (originalEq : data.original = original) (rootEq : data.observed.root = root)
    (traceEq : data.observed.trace = incomingTrace ring t replies q) :
    data = literalCallerData p original root ring t replies q := by
  cases data with
  | mk input observed =>
    cases observed with
    | mk image trace =>
      dsimp only at originalEq rootEq traceEq
      subst input image trace
      rfl

/-- Actual accepting source witnesses produce the path of ONE fixed adaptive
model. The state path, snapshot success, adjacent links, original input and
terminal restoration Boolean are all derived, not endpoint hypotheses. -/
theorem accepted_failure_statePath {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers)
    (w : FailureWitness layout program table) :
    StatePath (PCSBCSAdaptiveSourceCallerSnapshot.model layout program)
      table (Sampling.execute table program).2 false true := by
  classical
  let saved := w.saved
  let answers := PCSBCSSourceCallerAnswers.answers table
  let addresses : Keys → List Reference := address
  let ref : Reference := ⟨saved.root,initialShape saved.shape⟩
  let root := sourceRoot w.native.primitive addresses ref program table
  let native := nativeReplies w.original root w.native.strategy w.native.ring w.native.tape
  let old := Restoration.model p Q iv boundary
    (PCSBCSCapturedSourceStatePath.builder addresses ref program w.original saved)
  let next := PCSBCSAdaptiveSourceCallerSnapshot.model layout program
  let selected : List (Sigma Answers) := (packets w.native.final).map fun current =>
    ⟨.inl current,table (.inl current)⟩
  have checked := PCSBCSCapturedSourceAcceptance.accepted_failure_statePath
    w.native.primitive layout saved answers program table w.native.final w.original
    w.native.claims w.native.valid w.native.profile w.native.caller w.native.bound
    w.native.terminal w.native.recorded w.native.authentic w.native.clean w.native.ring
    w.native.tape w.native.strategy w.native.raws w.native.transport w.native.accepted w.native.failed
  have snapshots (current : EnteredPacket p Q iv boundary) (member : current ∈ packets w.native.final) :
      fromCapture addresses ref program w.original saved current (fun key => table key.val) =
        some (literalCallerData p w.original root w.native.ring w.native.tape native current.2.coord) := by
    obtain ⟨data,assembled,originalEq,rootEq,traceEq⟩ := checked.2.1 current member
    rw [data_literal w.original root w.native.ring w.native.tape native current.2.coord
      data originalEq rootEq traceEq] at assembled
    exact assembled
  have chosenPath : StatePath old table selected false true :=
    accepted_failure_path_of_snapshots addresses ref program w.original saved table
      (packets w.native.final) selected root w.native.ring w.native.tape w.native.strategy
      (by intro current member; exact List.mem_map.mpr ⟨current,member,rfl⟩)
      snapshots w.native.raws (packets_consecutive w.native.final w.native.terminal)
      (packets_initial w.native.final w.native.terminal)
      (packets_terminal w.native.final w.native.terminal) (packets_nonempty w.native.final)
      w.native.accepted w.native.failed
  have nodeEq (current : EnteredPacket p Q iv boundary) (member : current ∈ packets w.native.final) :
      publicNode next (.inl current) table = publicNode old (.inl current) table := by
    have constructed : PCSBCSSourceCallerOriginal.original p layout saved current.1.val answers =
        some w.original := by
      rw [packets_entry w.native.final current member]
      exact w.constructed
    have recovered : PCSBCSSourceSavedRecordDecoder.decode p current.1.val = some saved := by
      rw [packets_entry w.native.final current member]
      exact PCSBCSSourceSavedRecordProvenance.decode_saved_profileShape
        p layout saved w.native.final.1.val answers w.native.claims w.native.caller
        w.native.valid w.native.profile
    exact PCSBCSAdaptiveSourceCallerSnapshot.publicNode_original layout saved program current
      table w.original recovered constructed
  have beforeEq (key : Keys) (recorded : (⟨key,table key⟩ : Sigma Answers) ∈ selected) :
      before next key table = before old key table := by
    obtain ⟨current,member,same⟩ := List.mem_map.mp recorded
    have keyEq : .inl current = key := congrArg Sigma.fst same
    subst key
    unfold PCSStateRestoration.Latent.before
    rw [nodeEq current member]
    rfl
  have afterEq (key : Keys) (recorded : (⟨key,table key⟩ : Sigma Answers) ∈ selected) :
      after next key table = after old key table := by
    obtain ⟨current,member,same⟩ := List.mem_map.mp recorded
    have keyEq : .inl current = key := congrArg Sigma.fst same
    subst key
    unfold PCSStateRestoration.Latent.after
    rw [nodeEq current member]
    rfl
  have transported := path_transport old next table selected beforeEq afterEq chosenPath
  apply path_exposed_mono next table selected (Sampling.execute table program).2 _ transported
  intro event recorded
  obtain ⟨current,member,same⟩ := List.mem_map.mp recorded
  have actual := w.native.recorded current member
  rw [same] at actual
  exact actual

open Classical in
/-- Exact adaptive first-disclosure knowledge loss. Earlier caller coordinates
are actual source coins, reconstructed from erased values. The physical source
has Q requests total and the grouped source keeps index Q. This bounds the
explicit native-source relation outside the separately accounted Merkle bad
events; it is PCS-only and is not unconditional concrete hash security. -/
theorem failure_probability {R : Type}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Sampling Keys Answers R Q) :
    Soundness.uniformProb (Finset.univ.filter (Failed layout program)) ≤
      (Q : ℚ) * PCSRoundByRoundKnowledge.rbrError := by
  have nonnegative : (0 : ℚ) ≤ PCSRoundByRoundKnowledge.rbrError := by
    unfold PCSRoundByRoundKnowledge.rbrError SupportedCandidateExtraction.radiusEnvelope
    positivity
  have result := accepted_path_failure_probability
    (PCSBCSAdaptiveSourceCallerSnapshot.model layout program) Q 0 program
    PCSRoundByRoundKnowledge.rbrError nonnegative
    (PCSBCSAdaptiveSourceCallerSnapshot.conditional_hazard layout program)
    (Failed layout program) (by
      intro table failed
      obtain ⟨w⟩ := failed
      exact accepted_failure_statePath layout program table w)
  simpa only [Nat.add_zero] using result

#print axioms accepted_failure_statePath
#print axioms failure_probability
end Whir.PCSBCSAdaptiveSourceKnowledgeProbability
