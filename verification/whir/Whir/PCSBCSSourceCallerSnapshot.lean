import Whir.PCSBCSSourceRootCapture
import Whir.PCSBCSSourceReplyInversionIncoming
import Whir.PCSBCSSourcePacketTape
import Whir.PCSBCSCallerBinding
import Whir.PCSBCSSourceFrozenReplies

/-! Literal source snapshot assembly. The caller statement is a separately bound
input, never a truth premise. Root images come from first-mention capture; the
reply inverse consumes only strict Pending prefixes and checked frozen accesses.
The accepting-source transport and adjacent packet identities remain separate
obligations, rather than fields of this constructor. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceCallerSnapshot
open Concrete Protocol CausalGame CausalProbability FiatShamirGame
open PCSBCSChallengeOracle PCSBCSCallerBinding PCSBCSSourceReplyInversion
open PCSBCSMerkleRootCache PCSBCSSourceRootReferences

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}


open Classical PCSStateRestoration.Latent TypedOracleCompiler TypedFiatShamirGame
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- Only shapes literally addressed by the current source packet can enter its
snapshot. This excludes a root first mentioned after the current answer. -/
noncomputable def capturedRegistry {R : Type} {n : Nat}
    (address : Keys → List Reference) (program : Sampling Keys Answers R n)
    (current : EnteredPacket p Q iv boundary) (other : current.OtherValues) :
    PCSBCSSourceFrozenAccessor.Captures :=
  fun reference => if reference ∈ address (.inl current) then
    PCSBCSSourceRootCapture.captureOther address current reference program other else none

/-- At every enabled shape the erased packet reconstruction is the actual
first-mention capture, not an independently supplied oracle. -/
theorem capturedRegistry_actual {R : Type} {n : Nat}
    (address : Keys → List Reference) (program : Sampling Keys Answers R n)
    (current : EnteredPacket p Q iv boundary) (table : Table Keys Answers) :
    capturedRegistry address program current (fun other => table other.val) =
      fun reference => if reference ∈ address (.inl current) then
        PCSBCSSourceRootCapture.capture address reference program table else none := by
  funext reference
  by_cases mentioned : reference ∈ address (.inl current)
  · simp only [capturedRegistry,mentioned,↓reduceIte]
    exact PCSBCSSourceRootCapture.captureOther_table address current reference mentioned program table
  · simp only [capturedRegistry,mentioned,↓reduceIte]

/-- Every successful packet accessor uses the same first-disclosure capture for
a shared complete shape address, even when its strict prefix is longer. -/
theorem capturedRegistry_shared {R : Type} {n : Nat}
    (address : Keys → List Reference) (program : Sampling Keys Answers R n)
    (first second : EnteredPacket p Q iv boundary) (table : Table Keys Answers)
    (reference : Reference)
    (firstMentions : reference ∈ address (.inl first))
    (secondMentions : reference ∈ address (.inl second)) :
    capturedRegistry address program first (fun other => table other.val) reference =
      capturedRegistry address program second (fun other => table other.val) reference := by
  rw [capturedRegistry_actual,capturedRegistry_actual]
  simp only [firstMentions,secondMentions,↓reduceIte]

/-- Presence in one packet registry cannot be substituted for address
membership in another. Both gates must hold before sharing a captured root. -/
theorem capturedRegistry_enabled {R : Type} {n : Nat}
    (address : Keys → List Reference) (program : Sampling Keys Answers R n)
    (current : EnteredPacket p Q iv boundary) (table : Table Keys Answers)
    (reference : Reference) (mentions : reference ∈ address (.inl current)) :
    capturedRegistry address program current (fun other => table other.val) reference =
      PCSBCSSourceRootCapture.capture address reference program table := by
  rw [capturedRegistry_actual]
  simp only [mentions,↓reduceIte]

/-- A missing first-mention capture rejects, rather than fabricating a zero root.
A present partial capture still retains every cell's explicit availability. -/
noncomputable def fromCapture {R : Type} {n : Nat}
    (address : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (input : CallerInput p)
    (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (other : current.OtherValues) :
    Option (CallerData p) := do
  let registry := capturedRegistry address program current other
  let root ← registry ref
  let answers ← PCSBCSSourceFrozenReplies.replies current.2.coord saved registry
    current.2.messages (PCSBCSSourcePacketTape.strictPrefix current other)
  pure ⟨input, PCSBCSRestorationHazard.incomingData p root.raw
    (PCSBCSSourcePacketTape.ringPrefix current other)
    (PCSBCSSourcePacketTape.tape current other) answers current.2.coord⟩

/-- Concrete partial-registry assembly retains the independently bound caller,
not a caller reconstructed from the current oracle answer. -/
theorem captured_original_preserved {R : Type} {n : Nat}
    (address : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (input : CallerInput p)
    (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (other : current.OtherValues)
    (data : CallerData p)
    (assembled : fromCapture address ref program input saved current other = some data) :
    data.original = input := by
  unfold fromCapture at assembled
  obtain ⟨root,_,continued⟩ := Option.bind_eq_some_iff.mp assembled
  obtain ⟨answers,_,equal⟩ := Option.bind_eq_some_iff.mp continued
  cases Option.some.inj equal
  rfl

/-- A successful snapshot's root is the actual captured compact image. -/
theorem captured_root_provenance {R : Type} {n : Nat}
    (address : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (input : CallerInput p)
    (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (other : current.OtherValues)
    (data : CallerData p)
    (assembled : fromCapture address ref program input saved current other = some data) :
    ∃ root, ref ∈ address (.inl current) ∧
      PCSBCSSourceRootCapture.captureOther address current ref program other = some root ∧
      data.observed.root = root.raw := by
  unfold fromCapture at assembled
  obtain ⟨root,captured,continued⟩ := Option.bind_eq_some_iff.mp assembled
  obtain ⟨answers,_,equal⟩ := Option.bind_eq_some_iff.mp continued
  cases Option.some.inj equal
  by_cases mentioned : ref ∈ address (.inl current)
  · exact ⟨root,mentioned,by simpa only [capturedRegistry,mentioned,↓reduceIte] using captured,rfl⟩
  · simp only [capturedRegistry,mentioned,↓reduceIte] at captured
    cases captured

#print axioms captured_original_preserved
#print axioms captured_root_provenance
#print axioms capturedRegistry_actual
#print axioms capturedRegistry_shared
#print axioms capturedRegistry_enabled

/-- Only checked earlier-coordinate inverses enter the incoming public state,
at the same array index as the source Pending parser. -/
theorem captured_reply_preserved {R : Type} {count : Nat}
    (address : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R count) (input : CallerInput p)
    (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (other : current.OtherValues)
    (data : CallerData p)
    (assembled : fromCapture address ref program input saved current other = some data)
    (n : Nat) (earlier : n < position current.2.coord) :
    data.observed.trace.answers[n]! =
      ((PCSBCSSourceFrozenAccessor.inverseAt current.2.coord saved
        (capturedRegistry address program current other) current.2.messages
        (PCSBCSSourcePacketTape.strictPrefix current other) n).map Inverted.reply).getD default := by
  unfold fromCapture at assembled
  obtain ⟨root,_,continued⟩ := Option.bind_eq_some_iff.mp assembled
  obtain ⟨answers,parsed,equal⟩ := Option.bind_eq_some_iff.mp continued
  cases Option.some.inj equal
  rw [PCSBCSSourceFrozenReplies.replies_index current.2.coord saved
    (capturedRegistry address program current other) current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current other) answers parsed n earlier]
  change (PCSRoundByRoundTranscriptState.priorAnswers answers (position current.2.coord))[n]! =
    answers[n]?.getD default
  rw [PCSRoundByRoundTranscriptState.priorAnswers_get answers (position current.2.coord) n earlier]
  rw [getElem!_def]
  cases answers[n]? <;> rfl

#print axioms captured_reply_preserved

/-- Numerical rectangularity follows from the indexed padded capture even when
some images are unavailable. It is not a promise of authenticated availability. -/
theorem frozen_full_root (log : DuplexPublicSimulator.PublicLog) (digest : Digest32)
    (shape : PCSBCSMerkleRootCache.Shape) (lanes : Nat)
    (fits : shape.occupied ≤ shape.leafWords)
    (height : shape.height = (ParameterBounds.config p).logN -
      (ParameterBounds.config p).folds[0]! + (ParameterBounds.config p).rates[0]!)
    (occupied : shape.occupied = lanes) :
    PCSRoundByRoundSource.FullRoot (ParameterBounds.config p) lanes
      (freeze log digest shape).raw := by
  have rectangular := freeze_shape log digest shape fits
  constructor
  · simpa only [SupportedCandidateExtraction.blockLength,height] using rectangular.1
  · intro i
    exact (rectangular.2 _ (Array.getElem_mem_toList i.isLt)).trans occupied

#print axioms frozen_full_root

/-- Every bit of the selected full packet is absent from this constructor's
source inputs, not merely the challenge bytes consumed by the verifier. -/
theorem captured_snapshot_answer_independent {R : Type} {n : Nat}
    (address : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (input : CallerInput p)
    (saved : AnchoredHeaderCodec.Record)
    (current : EnteredPacket p Q iv boundary) (table : Table Keys Answers)
    (full : Fin (PCSBCSChallengeOracle.blocks
      (PCSBCSRounds.rawWidth current.2.coord)) → Digest32) :
    fromCapture address ref program input saved current
      (fun other => (Function.update table (.inl current) full) other.val) =
    fromCapture address ref program input saved current
      (fun other => table other.val) := by
  have same : (fun other : {key : Keys // key ≠ .inl current} =>
      (Function.update table (.inl current) full) other.val) =
      (fun other : {key : Keys // key ≠ .inl current} => table other.val) := by
    funext other
    simp only [Function.update_of_ne other.property]
  rw [same]

#print axioms captured_snapshot_answer_independent

end Whir.PCSBCSSourceCallerSnapshot
