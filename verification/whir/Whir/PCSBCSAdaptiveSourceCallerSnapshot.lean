import Whir.PCSBCSSourceCallerAnswers
import Whir.PCSBCSSourceCallerOriginal
import Whir.PCSBCSCapturedSourceStatePath
import Whir.PCSBCSSourceSavedRecordDecoder

/-! Actual adaptive caller metadata factors through OTHER source table values.
The literal fresh caller decoder and its existing original preparation retain
the genuine earlier source coins, while root addresses use only public packet
entry bytes. No selected packet bytes, including unused output bytes, are an
input to this latent reconstruction or cause another operational query. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSAdaptiveSourceCallerSnapshot
open Concrete Protocol CausalGame CausalProbability FiatShamirGame
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSSourceCallerSnapshot
open PCSBCSCallerBinding PCSBCSCapturedSourceTransport
open TypedOracleCompiler TypedFiatShamirGame PCSStateRestoration.Latent

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

noncomputable local instance (key : Keys) : Fintype (Answers key) :=
  Restoration.instFintypeAnswer p Q iv boundary key

/-- The actual partial constructor: source decoder, existing preparation,
first-mention root capture, and strict earlier native-reply inverse. Failures
remain None; no assumed compatible snapshot or successful oracle is supplied. -/
noncomputable def builder {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Sampling Keys Answers R n) : Restoration.Builder p Q iv boundary :=
  fun current other _ => do
    let saved ← PCSBCSSourceSavedRecordDecoder.decode p current.1.val
    let sourceAnswers := PCSBCSSourceCallerAnswers.answersFromOther current other
    let original ← PCSBCSSourceCallerOriginal.original p layout saved current.1.val sourceAnswers
    fromCapture address ⟨saved.root,initialShape saved.shape⟩
      program original saved current other

/-- Whole caller parsing sees only genuine bounded garbage-key values. Its
result, including the complete dependent prepared value and failures, is the
same for the actual source table and its erased completion. -/
theorem original_other (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (current packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) :
    PCSBCSSourceCallerOriginal.original p layout saved packet.1.val
      (PCSBCSSourceCallerAnswers.answersFromOther current (fun key => table key.val)) =
    PCSBCSSourceCallerOriginal.original p layout saved packet.1.val
      (PCSBCSSourceCallerAnswers.answers table) :=
  PCSBCSSourceCallerOriginal.original_prior_only p layout saved packet.1.val _ _
    (PCSBCSSourceCallerAnswers.caller_outputs_other current packet table)

/-- The denotational model is fixed outside the table average; actual earlier
caller coins and the complete adaptive saved record are reconstructed from
literal key metadata and erased values, not unrelated oracle callbacks. -/
noncomputable def model {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Sampling Keys Answers R n) : NodeModel Keys Answers (Option (CallerData p)) :=
  Restoration.model p Q iv boundary (builder layout program)

/-- Exact source assembly for every table, including parse/preparation errors.
All coordinates reached by the caller belong to the actual finite physical
source game; the outside-budget inert completion is not reached. -/
theorem publicNode_exact {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Sampling Keys Answers R n) (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) :
    publicNode (model layout program) (.inl current) table = (do
      let saved ← PCSBCSSourceSavedRecordDecoder.decode p current.1.val
      let original ← PCSBCSSourceCallerOriginal.original p layout saved current.1.val
        (PCSBCSSourceCallerAnswers.answers table)
      fromCapture address
        ⟨saved.root,initialShape saved.shape⟩ program original saved current
        (fun key => table key.val)) := by
  change (do
    let saved ← PCSBCSSourceSavedRecordDecoder.decode p current.1.val
    let original ← PCSBCSSourceCallerOriginal.original p layout saved current.1.val
      (PCSBCSSourceCallerAnswers.answersFromOther current (fun key => table key.val))
    fromCapture address
      ⟨saved.root,initialShape saved.shape⟩ program original saved current
      (fun key => table key.val)) = _
  apply congrArg (fun continuation : AnchoredHeaderCodec.Record → Option (CallerData p) =>
    (PCSBCSSourceSavedRecordDecoder.decode p current.1.val).bind continuation)
  funext saved
  rw [original_other layout saved current current table]

/-- A successful actual original constructor identifies the precise old-source
snapshot at this node. This is derived source equality, not a model-compatibility
premise. -/
theorem publicNode_original {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (program : Sampling Keys Answers R n) (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (original : CallerInput p)
    (recovered : PCSBCSSourceSavedRecordDecoder.decode p current.1.val = some saved)
    (constructed : PCSBCSSourceCallerOriginal.original p layout saved current.1.val
      (PCSBCSSourceCallerAnswers.answers table) = some original) :
    publicNode (model layout program) (.inl current) table =
      fromCapture address
        ⟨saved.root,initialShape saved.shape⟩ program original saved current
        (fun key => table key.val) := by
  have exactNode := publicNode_exact layout program current table
  apply exactNode.trans
  rw [recovered]
  change (PCSBCSSourceCallerOriginal.original p layout saved current.1.val
    (PCSBCSSourceCallerAnswers.answers table)).bind (fun input =>
      fromCapture address
        ⟨saved.root,initialShape saved.shape⟩ program input saved current
        (fun key => table key.val)) = _
  rw [constructed]
  rfl

/-- The additive conditional hazard applies to the actual adaptive erased
constructor. Its independent inputs are proved above, not asserted at the
Fiat-Shamir endpoint. -/
theorem conditional_hazard {R : Type} {n : Nat}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Sampling Keys Answers R n) :
    ConditionalHazard (model layout program) PCSRoundByRoundKnowledge.rbrError :=
  Restoration.conditional_hazard p Q iv boundary (builder layout program)

#print axioms original_other
#print axioms publicNode_exact
#print axioms publicNode_original
#print axioms conditional_hazard
end Whir.PCSBCSAdaptiveSourceCallerSnapshot
