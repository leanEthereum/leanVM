import Whir.PCSBCSSourceReplyInversion
import Whir.PCSBCSRestorationTrace

/-! Strict source-message prefixes supply precisely the reply indexes read by
incomingData. Challenges and the frozen oracle accessor remain parent inputs;
this is not a Fiat-Shamir endpoint or an authentication theorem. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceReplyInversion
open Concrete Protocol CausalGame CausalProbability WHIRHistory FiatShamirGame
open PCSBCSChallengeOracle PCSRoundByRoundTranscriptState

/-- No padding with default replies is needed: source packet position is the
exact length of the successfully decoded semantic response array. -/
theorem packet_reply_size {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {q : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry q) (frozen : FrozenOracles (ParameterBounds.config p))
    (answers : Array Reply) (parsed : replies frozen packet.messages = some answers) :
    answers.size = position q := by
  rw [packet_replies] at parsed
  exact prefixReplies_size frozen packet.messages (position q) answers parsed

theorem packet_reply_not_future {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {q : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry q) (frozen : FrozenOracles (ParameterBounds.config p))
    (answers : Array Reply) (parsed : replies frozen packet.messages = some answers)
    (n : Nat) (future : position q ≤ n) : answers[n]? = none := by
  apply Array.getElem?_eq_none
  rw [packet_reply_size packet frozen answers parsed]
  exact future

/-- Array positions in the incoming public trace are the same positions as the
source parser. In particular message n+1 gives semantic answer n. -/
theorem incoming_reply_index {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {q : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry q) (frozen : FrozenOracles (ParameterBounds.config p))
    (answers : Array Reply) (parsed : replies frozen packet.messages = some answers)
    (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p))
    (n : Nat) (earlier : n < position q) :
    ((PCSBCSRestorationHazard.incomingTrace ring t answers q).answers)[n]! =
      ((inverseAt frozen packet.messages n).map Inverted.reply).getD default := by
  rw [packet_reply_index packet frozen answers parsed n earlier]
  change (priorAnswers answers (position q))[n]! = answers[n]?.getD default
  rw [priorAnswers_get answers (position q) n earlier]
  rw [getElem!_def]
  cases answers[n]? <;> rfl

theorem incomingData_reply_index {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {q : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : SourcePacket p Q iv entry q) (frozen : FrozenOracles (ParameterBounds.config p))
    (answers : Array Reply) (parsed : replies frozen packet.messages = some answers)
    (root : BaseOracle) (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p))
    (n : Nat) (earlier : n < position q) :
    ((PCSBCSRestorationHazard.incomingData p root ring t answers q).trace.answers)[n]! =
      ((inverseAt frozen packet.messages n).map Inverted.reply).getD default :=
  incoming_reply_index packet frozen answers parsed ring t n earlier

#print axioms packet_reply_not_future
#print axioms incomingData_reply_index

#print axioms packet_reply_size
#print axioms incoming_reply_index
end Whir.PCSBCSSourceReplyInversion
