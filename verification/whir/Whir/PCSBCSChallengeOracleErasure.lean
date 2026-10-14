import Whir.PCSBCSChallengeOracleCanonical

/-! Strict source ancestors and erased-key ghost metadata. Predecessor packets
are constructed from the literal Pending-history suffix, with admission and path
bounds proved. Reading the OTHER virtual-table fibers reconstructs their Raw
values without consulting the selected packet. These are denotational ghost
functions, not an executable recovery oracle or ancestor-warming operation. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Whir.PCSBCSChallengeOracle
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open FiatShamirGame DuplexModeGame DuplexFraming RawOracleCoupling

namespace CanonicalPacket
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {entry : FramedHistory}

abbrev Earlier (current : CanonicalPacket p Q iv entry) :=
  {q : CausalProbability.Coordinate (ParameterBounds.config p) // position q < position current.coord}

def prefixMessages (current : CanonicalPacket p Q iv entry) (r : current.Earlier) : List Pending :=
  current.messages.drop (position current.coord-position r.val)

theorem messages_length (current : CanonicalPacket p Q iv entry) :
    current.messages.length = position current.coord+1 := by
  have positive := List.length_pos_iff.mpr current.2.nonempty
  change 0 < current.messages.length at positive
  have slot := current.2.position_eq
  change current.messages.length-1 = position current.coord at slot
  omega

theorem prefixMessages_length (current : CanonicalPacket p Q iv entry) (r : current.Earlier) :
    (current.prefixMessages r).length = position r.val+1 := by
  simp only [prefixMessages, List.length_drop, current.messages_length]
  have earlier := r.property
  omega

theorem prefixMessages_nonempty (current : CanonicalPacket p Q iv entry) (r : current.Earlier) :
    current.prefixMessages r ≠ [] := by
  apply List.length_pos_iff.mp
  rw [current.prefixMessages_length]
  omega

/-- Every strict chronological ancestor is itself an admitted canonical packet
within the SAME aggregate path cap, not an assumed reconstruction certificate. -/
def predecessor (current : CanonicalPacket p Q iv entry) (r : current.Earlier) :
    CanonicalPacket p Q iv entry :=
  ⟨r.val,
    { messages := current.prefixMessages r
      nonempty := current.prefixMessages_nonempty r
      admitted := scheduledAdmissible_drop _ current.messages _ current.2.admitted
      entryValid := current.2.entryValid
      position_eq := by rw [current.prefixMessages_length]; omega
      pathBound := by
        intro block
        have bound := WHIRCallerPrefix.pathCostFrom_drop (ParameterBounds.config p)
          (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
          (WHIRHistoryKey.stackWidth_positive p) entry current.messages
          (position current.coord-position r.val) block.val current.firstBlock.val
          current.2.nonempty (current.prefixMessages_nonempty r) current.2.admitted
        exact bound.trans (current.2.pathBound current.firstBlock) }⟩

theorem predecessor_ne_current (current : CanonicalPacket p Q iv entry) (r : current.Earlier) :
    current.predecessor r ≠ current := by
  intro same
  have slots := congrArg (fun a : CanonicalPacket p Q iv entry => position a.coord) same
  change position r.val = position current.coord at slots
  have earlier := r.property
  omega

/-- Exact distinctness of EVERY ancestor continuation key from EVERY selected
continuation key, rather than only distinctness of abstract coordinate labels. -/
theorem predecessor_block_key_ne (current : CanonicalPacket p Q iv entry) (r : current.Earlier)
    (past : Fin (blocks (rawWidth r.val))) (now : Fin (blocks (rawWidth current.coord))) :
    (current.predecessor r).2.key past ≠ current.2.key now := by
  intro same
  have histories := SourcePacket.distinct_history_keys
    (current.predecessor r).2 current.2 past now same
  have packetsSame : current.predecessor r = current := messages_injective histories.1
  exact current.predecessor_ne_current r packetsSame

abbrev OtherValues (current : CanonicalPacket p Q iv entry) :=
  (k : {k : (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).Key // k ≠ .inl current}) →
    (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).Answer (D := Digest32) k.val

/-- Pure ghost reconstruction from erased-table fibers. No allocation, oracle
request or source-visible read is inserted in the Atomic.program interpreter. -/
def prefixRawFromOther (current : CanonicalPacket p Q iv entry) (other : current.OtherValues)
    (r : current.Earlier) : Raw r.val :=
  grouped r.val (other ⟨.inl (current.predecessor r), by
    intro same
    exact current.predecessor_ne_current r (Sum.inl.inj same)⟩)

theorem prefixRaw_reconstructed (current : CanonicalPacket p Q iv entry)
    (table : (k : (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).Key) →
      (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).Answer (D := Digest32) k)
    (r : current.Earlier) :
    current.prefixRawFromOther (fun k => table k.val) r =
      grouped r.val (table (.inl (current.predecessor r))) := rfl

/-- The caller supplies its checked strict-prefix builder (e.g. incomingTrace).
All prover frames and the immutable statement/root are fixed in `current`;
additional public/Merkle ghost metadata can be computed from `other` as well. -/
def metadataFromOther {M : Type*} (current : CanonicalPacket p Q iv entry)
    (build : current.OtherValues → (∀ r : current.Earlier, Raw r.val) → M)
    (other : current.OtherValues) : M := build other (current.prefixRawFromOther other)

def metadataFromTable {M : Type*} (current : CanonicalPacket p Q iv entry)
    (build : current.OtherValues → (∀ r : current.Earlier, Raw r.val) → M)
    (table : (k : (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).Key) →
      (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).Answer (D := Digest32) k) : M :=
  current.metadataFromOther build (fun k => table k.val)

open Classical in
/-- Current-fiber erasure invariance of reconstructed metadata, even if the
builder inspects arbitrary other-table public/Merkle data. This theorem changes
only the virtual table's selected full packet, never prover input or raw keys. -/
theorem metadata_update_current {M : Type*} (current : CanonicalPacket p Q iv entry)
    (build : current.OtherValues → (∀ r : current.Earlier, Raw r.val) → M)
    (table : (k : (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).Key) →
      (partition (p := p) (Q := Q) (iv := iv) (entry := entry)).Answer (D := Digest32) k)
    (full : Fin (blocks (rawWidth current.coord)) → Digest32) :
    current.metadataFromTable build (Function.update table (.inl current) full) =
      current.metadataFromTable build table := by
  unfold metadataFromTable
  apply congrArg (current.metadataFromOther build)
  funext k
  simp [k.property]

end CanonicalPacket

#print axioms CanonicalPacket.predecessor
#print axioms CanonicalPacket.predecessor_block_key_ne
#print axioms CanonicalPacket.prefixRaw_reconstructed
#print axioms CanonicalPacket.metadata_update_current
end Whir.PCSBCSChallengeOracle
