import Whir.PCSBCSCapturedSourceTransport

/-! Finite literal-source caller answers at a fixed public frame boundary.
Bounded coordinates read the joined mixed partition table. Outside the physical
path budget both resolvers use the same inert zero digest; this completion is
not an actual source output. Every caller output of every entered packet is
admitted and physically bounded, and lies outside ALL entered packet fibers.
Thus the original caller decoder depends only on erased other values, including
when the selected full packet is replaced. Public root addresses instead read
only packet-entry bytes; they need no caller-answer independence premise. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceCallerAnswers
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open FiatShamirGame DuplexModeGame DuplexFraming RawOracleCoupling TypedFiatShamirGame
open PCSBCSChallengeOracle PCSBCSSourceRootReferences
open PCSStateRestoration.Latent

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "part" => EnteredPacket.partition
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- Actual finite-source lookup on bounded coordinates, with an explicitly inert
completion outside Q. No actual-output assertion is made outside Q. -/
noncomputable def answers (table : Table Keys Answers)
    (coordinate : FiatShamirGame.Coordinate) : Digest32 :=
  if bound : pathCost coordinate ≤ Q then
    (part).join table (.inr (constructionKey Q iv coordinate bound))
  else fun _ => 0

/-- Denotational resolver from erased values only. The selected packet's full
answer, including unused bytes, is not an input and is never read. -/
noncomputable def answersFromOther (current : EnteredPacket p Q iv boundary)
    (other : current.OtherValues) : FiatShamirGame.Coordinate → Digest32 :=
  answers (PCSBCSSourceRootCapture.otherTable current other)

theorem answers_bounded (table : Table Keys Answers)
    (coordinate : FiatShamirGame.Coordinate) (bound : pathCost coordinate ≤ Q) :
    answers table coordinate = (part).join table
      (.inr (constructionKey Q iv coordinate bound)) := by
  simp only [answers, dite_eq_left bound]

theorem answers_outside (table : Table Keys Answers)
    (coordinate : FiatShamirGame.Coordinate) (outside : ¬ pathCost coordinate ≤ Q) :
    answers table coordinate = (fun _ => 0) := by
  simp only [answers, dite_eq_right outside]

/-- Strict caller history is shorter than the common entry boundary; every
encoded entered source history contains at least that boundary many frames. -/
theorem caller_output_recognize_none (entry : FramedHistory)
    (entryBoundary : entry.frames.length = boundary)
    (entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f)
    (coordinate : FiatShamirGame.Coordinate)
    (member : coordinate ∈ WHIRCallerOutputs.callerOutputs entry)
    (bound : pathCost coordinate ≤ Q) :
    (part).recognize (.inr (constructionKey Q iv coordinate bound)) = none := by
  cases hit : (part).recognize (.inr (constructionKey Q iv coordinate bound)) with
  | none => rfl
  | some block =>
    have encoded := (part).encode_recognize _ block hit
    have keys : block.1.2.2.key block.2 = constructionKey Q iv coordinate bound :=
      Sum.inr.inj encoded
    have same := constructionKey_injective Q iv (block.1.2.2.valid block.2)
      (WHIRCallerOutputs.callerOutputs_admissible entry entryValid coordinate member)
      (block.1.2.2.pathBound block.2) bound keys
    have histories := congrArg FiatShamirGame.Coordinate.history same
    unfold SourcePacket.coordinate at histories
    rw [WHIRCallerPrefix.outputKeyFrom_history _ (WHIRHistoryKey.stackWidth_positive p)
      block.1.1.val (WHIRHistoryKey.scheduled_normal _ _
        block.1.2.2.nonempty block.1.2.2.admitted)] at histories
    have lengths := congrArg (fun h : FramedHistory => h.frames.length) histories
    have strict := (WHIRCallerOutputs.callerOutputs_strict_prefix entry coordinate member).2.2.1
    have sourceBoundary := block.1.1.property
    simp only [List.length_append] at lengths
    omega

/-- The entered packet's physical cap bounds every caller output; no extra
caller-bound promise is needed for the entered-packet endpoint. -/
theorem caller_output_bounded (packet : EnteredPacket p Q iv boundary)
    (coordinate : FiatShamirGame.Coordinate)
    (member : coordinate ∈ WHIRCallerOutputs.callerOutputs packet.1.val) :
    pathCost coordinate ≤ Q := by
  have earlier := WHIRCallerOutputs.callerOutputs_extended_pathCost_le packet.1.val
    coordinate member (WHIRHistoryKey.canonicalFrames
      (WHIRHistoryKey.stackWidth (ParameterBounds.config p)) packet.2.messages)
    (.output packet.2.firstBlock.val)
  have bounded := packet.2.2.pathBound packet.2.firstBlock
  change pathCost ⟨(WHIRCallerPrefix.outputKeyFrom
    (WHIRHistoryKey.stackWidth (ParameterBounds.config p)) packet.1.val
    packet.2.messages packet.2.firstBlock.val).history,
    .output packet.2.firstBlock.val⟩ ≤ Q at bounded
  simp only [CanonicalPacket.messages] at earlier bounded
  rw [WHIRCallerPrefix.outputKeyFrom_history _ (WHIRHistoryKey.stackWidth_positive p)
    packet.1.val (WHIRHistoryKey.scheduled_normal _ _
      packet.2.2.nonempty packet.2.2.admitted)] at bounded
  exact earlier.trans bounded

/-- Explicit validity and physical-bound hypotheses make this an actual finite
source-table answer, not the inert outside-budget completion. -/
theorem caller_output_actual (packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (coordinate : FiatShamirGame.Coordinate)
    (member : coordinate ∈ WHIRCallerOutputs.callerOutputs packet.1.val) :
    DuplexEncoding.Admissible coordinate ∧
      ∃ bound : pathCost coordinate ≤ Q,
        answers table coordinate = (part).join table
          (.inr (constructionKey Q iv coordinate bound)) ∧
        (part).recognize (.inr (constructionKey Q iv coordinate bound)) = none := by
  have bound := caller_output_bounded packet coordinate member
  exact ⟨WHIRCallerOutputs.callerOutputs_admissible _ packet.2.2.entryValid _ member,
    bound, answers_bounded table coordinate bound,
    caller_output_recognize_none _ packet.1.property packet.2.2.entryValid _ member bound⟩

/-- General-entry equality. If no physical bound is supplied, outside-budget
coordinates agree ONLY because both sides share the inert completion. -/
theorem caller_outputs_other_entry (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (entry : FramedHistory)
    (entryBoundary : entry.frames.length = boundary)
    (entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f)
    (coordinate : FiatShamirGame.Coordinate)
    (member : coordinate ∈ WHIRCallerOutputs.callerOutputs entry) :
    answersFromOther current (fun key => table key.val) coordinate = answers table coordinate := by
  classical
  unfold answersFromOther
  by_cases bound : pathCost coordinate ≤ Q
  · rw [answers_bounded _ _ bound, answers_bounded _ _ bound]
    have missed := caller_output_recognize_none (p := p) (iv := iv)
      entry entryBoundary entryValid coordinate member bound
    unfold Partition.join
    split
    · next block hit =>
      have impossible : some block = none := hit.symm.trans missed
      cases impossible
    · simp [PCSBCSSourceRootCapture.otherTable]
  · rw [answers_outside _ _ bound, answers_outside _ _ bound]

/-- This covers caller outputs of ANY entered packet, not just current. All
these coordinates have actual admitted/bounded answers by caller_output_actual. -/
theorem caller_outputs_other (current packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (coordinate : FiatShamirGame.Coordinate)
    (member : coordinate ∈ WHIRCallerOutputs.callerOutputs packet.1.val) :
    answersFromOther current (fun key => table key.val) coordinate = answers table coordinate :=
  caller_outputs_other_entry current table packet.1.val packet.1.property
    packet.2.2.entryValid coordinate member

theorem decode_other_entry (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (entry : FramedHistory)
    (entryBoundary : entry.frames.length = boundary)
    (entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f) :
    AnchoredSourceFreshCaller.decode layout saved entry
      (answersFromOther current (fun key => table key.val)) =
      AnchoredSourceFreshCaller.decode layout saved entry (answers table) := by
  unfold AnchoredSourceFreshCaller.decode
  rw [WHIRCallerClaims.entryTokens_prior_only entry _ _
    (caller_outputs_other_entry current table entry entryBoundary entryValid)]

theorem decode_other (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (current packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) :
    AnchoredSourceFreshCaller.decode layout saved packet.1.val
      (answersFromOther current (fun key => table key.val)) =
      AnchoredSourceFreshCaller.decode layout saved packet.1.val (answers table) :=
  decode_other_entry layout saved current table packet.1.val packet.1.property packet.2.2.entryValid

/-- Updating the selected full packet leaves the erased resolver unchanged at
EVERY coordinate, including its explicitly inert outside-budget completion. -/
theorem answersFromOther_update_current (current : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (full : EnteredPacket.Block current → Digest32) :
    answersFromOther current (fun key => (Function.update table (.inl current) full) key.val) =
      answersFromOther current (fun key => table key.val) := by
  classical
  apply congrArg (answersFromOther current)
  funext key
  simp [key.property]

theorem caller_outputs_update_current (current packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (full : EnteredPacket.Block current → Digest32)
    (coordinate : FiatShamirGame.Coordinate)
    (member : coordinate ∈ WHIRCallerOutputs.callerOutputs packet.1.val) :
    answers (Function.update table (.inl current) full) coordinate = answers table coordinate := by
  rw [← caller_outputs_other current packet _ coordinate member,
    answersFromOther_update_current, caller_outputs_other current packet table coordinate member]

theorem decode_update_current (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (current packet : EnteredPacket p Q iv boundary)
    (table : Table Keys Answers) (full : EnteredPacket.Block current → Digest32) :
    AnchoredSourceFreshCaller.decode layout saved packet.1.val
      (answers (Function.update table (.inl current) full)) =
      AnchoredSourceFreshCaller.decode layout saved packet.1.val (answers table) := by
  rw [← decode_other layout saved current packet _, answersFromOther_update_current,
    decode_other layout saved current packet table]

#print axioms answers
#print axioms answersFromOther
#print axioms answers_bounded
#print axioms answers_outside
#print axioms caller_output_recognize_none
#print axioms caller_output_bounded
#print axioms caller_output_actual
#print axioms caller_outputs_other_entry
#print axioms caller_outputs_other
#print axioms decode_other_entry
#print axioms decode_other
#print axioms answersFromOther_update_current
#print axioms caller_outputs_update_current
#print axioms decode_update_current
end Whir.PCSBCSSourceCallerAnswers
