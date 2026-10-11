import Whir.PCSBCSChallengeOracleEnteredPartition

/-! All varying live prefixes share one virtual source table. Strict ancestors
retain the same public entry boundary and reside in OTHER packet fibers. Pure
metadata reconstruction does not request or disclose their latent answers. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Whir.PCSBCSChallengeOracle.EnteredPacket
open Concrete Protocol CausalGame CausalProbability PCSBCSRounds
open FiatShamirGame DuplexModeGame RawOracleCoupling
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}

abbrev Earlier (current : EnteredPacket p Q iv boundary) := current.2.Earlier

def predecessor (current : EnteredPacket p Q iv boundary) (earlier : current.Earlier) :
    EnteredPacket p Q iv boundary := ⟨current.1,current.2.predecessor earlier⟩

theorem predecessor_ne_current (current : EnteredPacket p Q iv boundary)
    (earlier : current.Earlier) : current.predecessor earlier ≠ current := by
  intro same
  have positions := congrArg (fun a : EnteredPacket p Q iv boundary => position a.2.coord) same
  change position earlier.val = position current.2.coord at positions
  have strict := earlier.property
  omega

abbrev OtherValues (current : EnteredPacket p Q iv boundary) :=
  (k : {k : (partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Key //
      k ≠ .inl current}) →
    (partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Answer (D := Digest32) k.val

def prefixRawFromOther (current : EnteredPacket p Q iv boundary)
    (other : current.OtherValues) (earlier : current.Earlier) : Raw earlier.val :=
  grouped earlier.val (other ⟨.inl (current.predecessor earlier),by
    intro same
    exact current.predecessor_ne_current earlier (Sum.inl.inj same)⟩)

def metadataFromOther {M : Type*} (current : EnteredPacket p Q iv boundary)
    (build : current.OtherValues → (∀ r : current.Earlier, Raw r.val) → M)
    (other : current.OtherValues) : M := build other (current.prefixRawFromOther other)

def metadataFromTable {M : Type*} (current : EnteredPacket p Q iv boundary)
    (build : current.OtherValues → (∀ r : current.Earlier, Raw r.val) → M)
    (table : (k : (partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Key) →
      (partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Answer (D := Digest32) k) : M :=
  current.metadataFromOther build (fun key => table key.val)

open Classical in
theorem metadata_update_current {M : Type*} (current : EnteredPacket p Q iv boundary)
    (build : current.OtherValues → (∀ r : current.Earlier, Raw r.val) → M)
    (table : (k : (partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Key) →
      (partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Answer (D := Digest32) k)
    (full : Fin (blocks (rawWidth current.2.coord)) → Digest32) :
    current.metadataFromTable build (Function.update table (.inl current) full) =
      current.metadataFromTable build table := by
  unfold metadataFromTable
  apply congrArg (current.metadataFromOther build)
  funext key
  simp [key.property]

#print axioms predecessor_ne_current
#print axioms metadata_update_current
end Whir.PCSBCSChallengeOracle.EnteredPacket
