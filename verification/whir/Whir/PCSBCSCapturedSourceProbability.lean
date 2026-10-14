import Whir.PCSBCSCapturedSourceAcceptance
import Whir.PCSBCSChallengeOracleEnteredGames

/-! PCS-only source-game composition with fixed caller metadata. The failure
relation uses the literal caller decoder, native acceptance, the actual decoder
extractor, and explicit native primitive/codec evidence. It does not accept a
StatePath, restoration Boolean, compatible snapshot, or probability certificate.
The source answers and original caller in this module are fixed outside the
table average, but public root addresses have no caller-answer input. Adaptive
earlier caller coins require the separate erased-value adapter.
The indexed atomic source has Q draws, not Q per prover round. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSCapturedSourceProbability
open Concrete Protocol CausalGame CausalProbability FiatShamirGame
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSSourceCallerSnapshot
open PCSBCSCallerBinding PCSBCSCapturedSourceAcceptance
open PCSBCSCapturedSourceTransport PCSBCSCapturedSourceStatePath
open PCSBCSCapturedNativeReplyBridge PCSBCSRestorationHazard PCSRoundByRoundTranscriptState
open TypedOracleCompiler TypedFiatShamirGame PCSStateRestoration.Latent
open PublicMerkleLog MerkleTransport.Commitments

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

noncomputable local instance (key : Keys) : Fintype (Answers key) :=
  Restoration.instFintypeAnswer p Q iv boundary key

/-- Literal accepted source run outside the separately charged Merkle bad
 events. Every root and native reply is derived from the same primitive and
 first-captured prefix. The caller is independently fixed; no honesty of its
 original claims is assumed. -/
structure FailureWitness {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (answers : FiatShamirGame.Coordinate → Digest32)
    (program : Sampling Keys Answers R n) (original : CallerInput p)
    (table : Table Keys Answers) where
  primitive : DuplexModeGame.PrimitiveOracle
  final : EnteredPacket p Q iv boundary
  claims : AnchoredSourceCaller.Claims
  valid : saved.Valid
  profile : profileShape p saved.shape
  caller : AnchoredSourceFreshCaller.decode layout saved final.1.val answers = some claims
  bound : BoundOriginal original saved claims
  terminal : final.2.coord = lastCoordinate (ParameterBounds.config p)
  recorded : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
    (⟨.inl current,table (.inl current)⟩ : Sigma Answers) ∈ (Sampling.execute table program).2
  authentic : AuthenticLog primitive (sourceLog address
    ⟨saved.root,initialShape saved.shape⟩ program table)
  clean : ¬ OutputCollision (sourceLog address
    ⟨saved.root,initialShape saved.shape⟩ program table)
  ring : RingPCSGame.Prefix
  tape : Tape (ParameterBounds.config p)
  strategy : RingPCSGame.Prefix → Strategy
  raws : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
    grouped current.2.coord (table (.inl current)) =
      literalRaw ring tape current.2.coord
  transport : ∀ current ∈ PCSBCSCapturedSourceStatePath.packets final,
    ReplyTransport address program table primitive saved current
      (nativeReplies original
        (sourceRoot primitive address
          ⟨saved.root,initialShape saved.shape⟩ program table) strategy ring tape)
  accepted : experiment (OriginalClaimsChecker.input original.prepared
    (sourceRoot primitive address
      ⟨saved.root,initialShape saved.shape⟩ program table) ring) (strategy ring) tape = true
  failed : ¬ ∃ w,
    PCSRoundByRoundKnowledge.extract p original.lanes original.family original.points
      original.anchorPoint original.anchorValue
      (sourceRoot primitive address
        ⟨saved.root,initialShape saved.shape⟩ program table) = some w ∧
    PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) original.lanes
      (sourceRoot primitive address
        ⟨saved.root,initialShape saved.shape⟩ program table)
      original.family original.points original.anchorPoint original.anchorValue w

/-- The source relation, not a free assumed accepted path. -/
def Failed {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (answers : FiatShamirGame.Coordinate → Digest32)
    (program : Sampling Keys Answers R n) (original : CallerInput p)
    (table : Table Keys Answers) : Prop :=
  Nonempty (FailureWitness layout saved answers program original table)

open Classical in
/-- Exact first-disclosure loss for the actual captured adapter with fixed
source callback and original caller. The physical compiler and atomic grouping
both retain index Q; this is not the adaptive-caller Fiat-Shamir endpoint. -/
theorem fixed_metadata_failure_probability {R : Type}
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (answers : FiatShamirGame.Coordinate → Digest32)
    (program : Sampling Keys Answers R Q) (original : CallerInput p) :
    Soundness.uniformProb (Finset.univ.filter
      (Failed layout saved answers program original)) ≤
      (Q : ℚ) * PCSRoundByRoundKnowledge.rbrError := by
  let model := Restoration.model p Q iv boundary
    (builder address ⟨saved.root,initialShape saved.shape⟩
      program original saved)
  have nonnegative : (0 : ℚ) ≤ PCSRoundByRoundKnowledge.rbrError := by
    unfold PCSRoundByRoundKnowledge.rbrError SupportedCandidateExtraction.radiusEnvelope
    positivity
  have result := accepted_path_failure_probability model Q 0 program
    PCSRoundByRoundKnowledge.rbrError nonnegative
    (Restoration.conditional_hazard p Q iv boundary
      (builder address ⟨saved.root,initialShape saved.shape⟩
        program original saved))
    (Failed layout saved answers program original) (by
      intro table failed
      obtain ⟨w⟩ := failed
      exact (accepted_failure_statePath w.primitive layout saved answers program table
        w.final original w.claims w.valid w.profile w.caller w.bound w.terminal
        w.recorded w.authentic w.clean w.ring w.tape w.strategy w.raws w.transport
        w.accepted w.failed).2.2)
  simpa only [Nat.add_zero] using result

#print axioms fixed_metadata_failure_probability
end Whir.PCSBCSCapturedSourceProbability
