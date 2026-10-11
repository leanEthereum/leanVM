import Whir.PCSBCSChallengeOracle
import Whir.WHIRCallerOutputs

/-! Actual #552/source12ee modeled source-history adapter, not the book's
challenge hash chain or a historical Rust-byte identity. Literal prior
caller/anchor frames and the current Pending prover string select every
continuation block. Merkle and arbitrary chosen-CV requests remain in the public
compression Program and the aggregate Counts ledger. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Whir.PCSBCSChallengeOracle
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open FiatShamirGame DuplexModeGame TypedOracleCompiler DuplexRefinement DuplexFraming

/-- The explicit source/model interface fixes the actual live entry and admitted
prover strings. It does not assume random source bytes or a hash-chain compiler. -/
structure SourcePacket (p : ParameterBounds.Profile) (Q : Nat)
    (iv : Digest32) (entry : FramedHistory) (q : CausalProbability.Coordinate (ParameterBounds.config p)) where
  messages : List Pending
  nonempty : messages ≠ []
  admitted : scheduledAdmissible (ParameterBounds.config p) messages = true
  entryValid : ∀ f ∈ entry.frames, DuplexEncoding.FrameValid f
  position_eq : messages.length-1 = position q
  pathBound : ∀ block : Fin (blocks (rawWidth q)), pathCost
    (WHIRCallerPrefix.outputKeyFrom (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
      entry messages block.val) ≤ Q

namespace SourcePacket
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
  {entry : FramedHistory} {q : CausalProbability.Coordinate (ParameterBounds.config p)}

theorem width_eq (s : SourcePacket p Q iv entry q) :
    WHIRHistoryKey.stackWidth (ParameterBounds.config p) (s.messages.length-1) = 24*rawWidth q := by
  unfold WHIRHistoryKey.stackWidth
  rw [s.position_eq, schedule_get_position]
  rfl

def coordinate (s : SourcePacket p Q iv entry q) (block : Fin (blocks (rawWidth q))) :
    FiatShamirGame.Coordinate := WHIRCallerPrefix.outputKeyFrom
      (WHIRHistoryKey.stackWidth (ParameterBounds.config p)) entry s.messages block.val

theorem valid (s : SourcePacket p Q iv entry q) (block : Fin (blocks (rawWidth q))) :
    DuplexEncoding.Admissible (s.coordinate block) := by
  apply WHIRCallerPrefix.production_stackOutputKeyFrom_admissible p entry s.entryValid
    s.messages block.val s.nonempty s.admitted
  simpa only [s.width_eq, blocks] using block.isLt

def key (s : SourcePacket p Q iv entry q) (block : Fin (blocks (rawWidth q))) : RawKey Q :=
  constructionKey Q iv (s.coordinate block) (s.pathBound block)

theorem key_injective (s : SourcePacket p Q iv entry q) : Function.Injective s.key := by
  intro a b same
  have coordinates := constructionKey_injective Q iv (s.valid a) (s.valid b)
    (s.pathBound a) (s.pathBound b) same
  have terminal := congrArg FiatShamirGame.Coordinate.terminal coordinates
  exact Fin.ext (Terminal.output.inj terminal)

/-- This is the challenge model itself: a finite programmable raw RO keyed by
the literal #552 message/template encoding. No compressed challenge-chain state
replaces the source history. -/
def sample (s : SourcePacket p Q iv entry q) (ro : RawKey Q → Digest32) : Raw q :=
  grouped q (fun b => ro (s.key b))

/-- Operative physical byte mapping, including scalar slices that cross output
blocks. Represents and the successful guarded squeeze are the existing actual
source-machine preconditions; no fresh-entropy or hash-chain premise is used. -/
theorem physical_packet_bytes (s : SourcePacket p Q iv entry q)
    (compress : Compression) (before after : State) (bytes : List Byte)
    (represents : Represents compress iv
      (WHIRCallerPrefix.beforeModelFrom (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
        entry s.messages) before)
    (squeezed : squeeze compress before (rawWidth q*24) = .ok (after,bytes)) :
    bytes = List.ofFn (vectorBytes (rawWidth q) (rawVector q
      (grouped q (fun b => evalCoordinate compress iv (s.coordinate b))))) := by
  rw [WHIRCallerPrefix.squeeze_frame_bytes_from compress iv _
    (WHIRHistoryKey.stackWidth_positive p) entry
    (WHIRHistoryKey.scheduled_normal _ _ s.nonempty s.admitted) before after
    represents _ bytes squeezed, WHIRCallerOutputs.stream_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [grouped_payload_bytes]
  simp only [Nat.zero_add, evalCoordinate, coordinate, WHIRCallerPrefix.outputKeyFrom, evalTerminal]

open Classical in
/-- Full-E conditional law includes initial eight-E, query vector and lambda,
and every individual fold/OOD/tail coordinate, by the dependent Raw alphabet. -/
theorem fresh_uniform_independent (s : SourcePacket p Q iv entry q)
    (cache : RawKey Q → Option Digest32) (fresh : ∀ b, cache (s.key b) = none)
    (P : Raw q → Prop) (observer : ({k : RawKey Q // k ∉ Set.range s.key} → Digest32) → Prop) :
    letI : DecidableEq (RawKey Q) := Classical.decEq _
    letI := rawKeyFintype Q
    SamplingProbability.probability (fun ro : RawKey Q → Digest32 =>
      P (s.sample (RawOracleCoupling.overlay cache ro)) ∧
      observer (restrictionEquiv s.key s.key_injective ro).2) =
      SamplingProbability.probability P * SamplingProbability.probability observer := by
  let : DecidableEq (RawKey Q) := Classical.decEq _
  let := rawKeyFintype Q
  exact @fresh_group_independent (RawKey Q) (rawKeyFintype Q) (ParameterBounds.config p)
    q s.key s.key_injective cache fresh P observer

/-- Literal histories, including the current message and continuation index,
are injective across all admitted source-round packets at the same entry. -/
theorem distinct_history_keys {q' : CausalProbability.Coordinate (ParameterBounds.config p)}
    (s : SourcePacket p Q iv entry q) (t : SourcePacket p Q iv entry q')
    (a : Fin (blocks (rawWidth q))) (b : Fin (blocks (rawWidth q')))
    (same : s.key a = t.key b) : s.messages = t.messages ∧ a.val = b.val := by
  have coordinates := constructionKey_injective Q iv (s.valid a) (t.valid b)
    (s.pathBound a) (t.pathBound b) same
  exact WHIRCallerPrefix.outputKeyFrom_injective _ _
    (WHIRHistoryKey.stackWidth_positive p) (WHIRHistoryKey.stackWidth_positive p) entry
    (WHIRHistoryKey.scheduled_normal _ _ s.nonempty s.admitted)
    (WHIRHistoryKey.scheduled_normal _ _ t.nonempty t.admitted) _ _ coordinates

/-- One block is exactly the ideal construction answer, while all public
primitive (including Merkle-domain) requests still use the simulator. -/
theorem ideal_block (s : SourcePacket p Q iv entry q)
    {Seed State R : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (state : State) (b : Fin (blocks (rawWidth q)))
    (next : Digest32 → Program R)
    (counted : Counts Q (.ask (.construction (s.coordinate b) (s.valid b)) next)) :
    (runIdeal sim ro iv state (.ask (.construction (s.coordinate b) (s.valid b)) next)
      Q (by rfl) counted).view.observations.head? =
        some ⟨.construction (s.coordinate b) (s.valid b), ro (s.key b)⟩ := by
  rfl

end SourcePacket

/-- All observers of any decoded challenge/protocol/public-primitive view are
covered. Counts charges uncached construction paths, repeats, nonce terminals,
continuation blocks, and direct Merkle calls in one Q; it is not just a count of
PCS coordinates. This transports to the actual literal-history RO, not to BCS. -/
theorem literal_source_mode_bound {AdvCoins R V : Type} [Fintype AdvCoins]
    (Q : Nat) (iv : Digest32) (adversary : AdvCoins → Program R)
    (counted : ∀ a, Counts Q (adversary a)) (decode : View R → V) (D : V → Bool) :
    letI := DuplexPublicSimulator.seedFintype
    |realProbability iv adversary (fun view => D (decode view)) -
      idealProbability (DuplexPublicSimulator.simulator Q) iv adversary counted
        (fun view => D (decode view))| ≤ duplexModeLoss Q :=
  PublicCompressionCouplingActualJoint.actual_modeAdv_le_duplexModeLoss Q iv adversary counted _

open Classical in
/-- The event mapping is the proved actual joint causal bad event, not an
assumed RO-equivalence certificate. Arbitrary decoded views coincide outside it. -/
theorem literal_source_good_view {R V : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) {trace}
    {pair : PublicCompressionCouplingActualJoint.JointResult Q R}
    (execution : Sampling.Runs (PublicCompressionCouplingActualJoint.actualJoint Q iv p counted) trace pair)
    (table : PublicCompressionCouplingMixed.Key Q → Digest32)
    (quiet : PublicCompressionCouplingMixed.causalBad Q iv p counted
      (RawOracleCoupling.overlay pair.2.2 table) = false)
    (decode : View R → V) : decode pair.1.1.view = decode pair.2.1.1 := by
  exact congrArg decode (PublicCompressionCouplingSourceStream.actual_joint_good_view
    Q iv p counted execution table quiet)

#print axioms SourcePacket.physical_packet_bytes
#print axioms SourcePacket.fresh_uniform_independent
#print axioms SourcePacket.distinct_history_keys
#print axioms SourcePacket.ideal_block
#print axioms literal_source_mode_bound
#print axioms literal_source_good_view
end Whir.PCSBCSChallengeOracle
