import Whir.PCSBCSChallengeOraclePackets

/-! The canonical finite packet domain contains EVERY admitted source history
under the aggregate path cap, not an arbitrarily preselected family of observer
queries. Finiteness is derived from the proved literal key injection. All
nonpacket raw and simulator-seed inputs remain in the garbage summand. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Whir.PCSBCSChallengeOracle
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open FiatShamirGame DuplexModeGame RawOracleCoupling

abbrev CanonicalPacket (p : ParameterBounds.Profile) (Qcompression : Nat)
    (iv : Digest32) (entry : FramedHistory) :=
  Sigma (fun q : CausalProbability.Coordinate (ParameterBounds.config p) =>
    SourcePacket p Qcompression iv entry q)

namespace CanonicalPacket
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {entry : FramedHistory}

def coord (packet : CanonicalPacket p Q iv entry) := packet.1

def messages (packet : CanonicalPacket p Q iv entry) := packet.2.messages

theorem messages_injective :
    Function.Injective (messages (p := p) (Q := Q) (iv := iv) (entry := entry)) := by
  intro a b same
  rcases a with ⟨q,s⟩
  rcases b with ⟨q',t⟩
  change s.messages = t.messages at same
  have position_same : position q = position q' := by
    rw [← s.position_eq, ← t.position_eq, same]
  have coordinate_same : q = q' := by
    have hs := schedule_get_position q
    have ht := schedule_get_position q'
    rw [position_same] at hs
    exact Option.some.inj (hs.symm.trans ht)
  subst q'
  have records_same : s = t := by
    cases s
    cases t
    cases same
    rfl
  cases records_same
  rfl

def firstBlock (packet : CanonicalPacket p Q iv entry) : Fin (blocks (rawWidth packet.coord)) :=
  ⟨0, by
    have positive := (WHIRHistoryKey.production_sample_counts p packet.coord).2
    change 0 < rawWidth packet.coord at positive
    unfold blocks
    omega⟩

def firstKey (packet : CanonicalPacket p Q iv entry) : RawKey Q := packet.2.key packet.firstBlock

theorem firstKey_injective :
    Function.Injective (firstKey (p := p) (Q := Q) (iv := iv) (entry := entry)) := by
  intro a b same
  have facts := SourcePacket.distinct_history_keys a.2 b.2 a.firstBlock b.firstBlock same
  exact messages_injective facts.1

/-- A checked finite domain of ALL source packets; no finite-enumeration
coverage assumption and no source entropy assumption are needed. -/
noncomputable instance : Fintype (CanonicalPacket p Q iv entry) := by
  classical
  letI := rawKeyFintype Q
  exact Fintype.ofInjective firstKey firstKey_injective

noncomputable instance : DecidableEq (CanonicalPacket p Q iv entry) := Classical.decEq _

noncomputable def partition :
    Partition (PublicCompressionCouplingMixed.Key Q) (CanonicalPacket p Q iv entry)
      (fun a => Fin (blocks (rawWidth a.coord))) :=
  sourceFamilyPartition coord (fun a => a.2) messages_injective

set_option maxHeartbeats 0 in
/-- Every admitted physical source output block is recognized as its full
canonical packet; remaining simulator or observer keys are not excluded. -/
theorem recognize_block (packet : CanonicalPacket p Q iv entry)
    (b : Fin (blocks (rawWidth packet.coord))) :
    (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).recognize
      (.inr (packet.2.key b)) = some ⟨packet,b⟩ :=
  (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).recognize_encode ⟨packet,b⟩

end CanonicalPacket

#print axioms CanonicalPacket.messages_injective
#print axioms CanonicalPacket.firstKey_injective
#print axioms CanonicalPacket.recognize_block
end Whir.PCSBCSChallengeOracle
