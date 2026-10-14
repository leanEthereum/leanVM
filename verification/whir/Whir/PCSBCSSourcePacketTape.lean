import Whir.PCSBCSChallengeOracleEnteredErasure
import Whir.WHIRFiatShamir

/-! Pure strict-prefix reconstruction from OTHER full source-packet fibers.
No oracle operation or ancestor-warming draw occurs here. The source metadata
assumptions are exactly SourcePacket's admitted Pending list, entry validity,
position equality, and aggregate path bound. A table is one shared, memoized
whole-packet table, not a recovery oracle. Caller snapshots, reply inversion,
frozen root accessors and acceptance are deliberately supplied by callers.
These lemmas do not assert a Fiat-Shamir endpoint. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourcePacketTape
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open PCSBCSChallengeOracle FiatShamirGame DuplexModeGame

/-- Initial Raw is ring-prefix × initial E; all other alphabets are Sample. -/
def project {c : Config} (q : Coordinate c) : Raw q → Sample q :=
  match q with
  | .initial => Prod.snd
  | .fold _ _ => id
  | .ood _ _ => id
  | .query _ => id
  | .tail _ => id

abbrev RawPrefix {c : Config} (q : Coordinate c) :=
  (r : Coordinate c) → position r < position q → Raw r

/-- Named inert suffix: never sampled and never an incoming predicate input. -/
def inertSample {c : Config} (q : Coordinate c) : Sample q := 0

def inertRing : RingPCSGame.Prefix := (0, fun _ => 0)

/-- Executable realization of the existing strict-prefix tape convention. -/
def tapeOfPrefix {c : Config} {q : Coordinate c} (past : WHIRFiatShamir.Prefix q) : Tape c :=
  (coordinates c).symm (fun r => if h : position r < position q then past r h else inertSample r)

def projectedPrefix {c : Config} {q : Coordinate c} (past : RawPrefix q) :
    WHIRFiatShamir.Prefix q := fun r h => project r (past r h)

def ringOfPrefix {c : Config} {q : Coordinate c} (past : RawPrefix q) : RingPCSGame.Prefix :=
  if h : position (.initial : Coordinate c) < position q then (past .initial h).1 else inertRing

/-- Unlike the inert totalized ring, this is safe to expose to a public predicate. -/
def disclosedRing {c : Config} {q : Coordinate c} (past : RawPrefix q) :
    Option RingPCSGame.Prefix :=
  if h : position (.initial : Coordinate c) < position q then some (past .initial h).1 else none

theorem tapeOfPrefix_eq {c : Config} {q : Coordinate c} (past : WHIRFiatShamir.Prefix q) :
    tapeOfPrefix past = past.tape := rfl

theorem get_tapeOfPrefix {c : Config} {q r : Coordinate c}
    (past : WHIRFiatShamir.Prefix q) (h : position r < position q) :
    get r (tapeOfPrefix past) = past r h := by
  change (coordinates c ((coordinates c).symm _)) r = _
  simp only [Equiv.apply_symm_apply, dite_eq_left h]

theorem get_inert {c : Config} {q r : Coordinate c}
    (past : WHIRFiatShamir.Prefix q) (h : ¬ position r < position q) :
    get r (tapeOfPrefix past) = inertSample r := by
  change (coordinates c ((coordinates c).symm _)) r = _
  simp only [Equiv.apply_symm_apply, dite_eq_right h]

/-- Incoming predicates receive only RawPrefix, not the total tape or its
inert ring. This interface also lets the caller attach Array Reply and its
checked snapshot through a fixed closure, without exposing future values. -/
def incoming {c : Config} {q : Coordinate c} (P : RawPrefix q → Prop)
    (past : RawPrefix q) : Prop := P past

/-- Any choice of inert suffix gives exactly the same incoming prefix. -/
theorem incoming_ignores_suffix {c : Config} {q : Coordinate c}
    (past : RawPrefix q) (suffix : ∀ r : Coordinate c, Sample r)
    (P : WHIRFiatShamir.Prefix q → Prop) :
    P (WHIRFiatShamir.Prefix.ofTape q
      ((coordinates c).symm (fun r => if h : position r < position q
        then project r (past r h) else suffix r))) ↔ P (projectedPrefix past) := by
  have same : WHIRFiatShamir.Prefix.ofTape q
      ((coordinates c).symm (fun r => if h : position r < position q
        then project r (past r h) else suffix r)) = projectedPrefix past := by
    funext r h
    change (coordinates c ((coordinates c).symm _)) r = _
    simp only [Equiv.apply_symm_apply, dite_eq_left h, projectedPrefix]
  rw [same]

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}

abbrev Table :=
  (k : (EnteredPacket.partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Key) →
    (EnteredPacket.partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Answer
      (D := Digest32) k

def rawPrefix (current : EnteredPacket p Q iv boundary) (other : current.OtherValues) :
    RawPrefix current.2.coord := fun r h => current.prefixRawFromOther other ⟨r,h⟩

def strictPrefix (current : EnteredPacket p Q iv boundary) (other : current.OtherValues) :
    WHIRFiatShamir.Prefix current.2.coord := projectedPrefix (rawPrefix current other)

def tape (current : EnteredPacket p Q iv boundary) (other : current.OtherValues) :
    Tape (ParameterBounds.config p) := tapeOfPrefix (strictPrefix current other)

def ringPrefix (current : EnteredPacket p Q iv boundary) (other : current.OtherValues) :
    RingPCSGame.Prefix := ringOfPrefix (rawPrefix current other)

theorem rawPrefix_table (current : EnteredPacket p Q iv boundary)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary)) (r : current.Earlier) :
    rawPrefix current (fun k => table k.val) r.val r.property =
      grouped r.val (table (.inl (current.predecessor r))) := rfl

/-- Every earlier coordinate reads its actual global-table predecessor packet. -/
theorem get_table (current : EnteredPacket p Q iv boundary)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary)) (r : current.Earlier) :
    get r.val (tape current (fun k => table k.val)) =
      project r.val (grouped r.val (table (.inl (current.predecessor r)))) :=
  get_tapeOfPrefix _ r.property

/-- The byte law is the existing contiguous grouped payload law, including
cross-block scalar slices; no cardinality-selected representation is used. -/
theorem rawPrefix_bytes (current : EnteredPacket p Q iv boundary)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary)) (r : current.Earlier)
    (j : Fin (rawWidth r.val * 24)) :
    vectorBytes (rawWidth r.val) (rawVector r.val
      (rawPrefix current (fun k => table k.val) r.val r.property)) j =
      table (.inl (current.predecessor r)) ⟨j.val / 32, by
        change j.val / 32 < blocks (rawWidth r.val)
        have bound := packet_length (rawWidth r.val)
        have hj := j.isLt
        omega⟩ ⟨j.val % 32, Nat.mod_lt _ (by decide)⟩ :=
  grouped_payload_bytes r.val _ j

open Classical in
/-- All reconstruction products, including any fixed caller combination,
ignore a replacement of the WHOLE selected packet (unused bytes included). -/
theorem reconstruction_update_current {M : Type*} (current : EnteredPacket p Q iv boundary)
    (build : RawPrefix current.2.coord → M)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary))
    (full : Fin (blocks (rawWidth current.2.coord)) → Digest32) :
    build (rawPrefix current (fun k => Function.update table (.inl current) full k.val)) =
      build (rawPrefix current (fun k => table k.val)) := by
  exact current.metadata_update_current (fun _ past => build (fun r h => past ⟨r,h⟩)) table full

/-- Nested literal Pending suffixes give the same admitted source packet.
Both packets retain the identical live entry and the same aggregate cap. -/
theorem predecessor_comp (current : EnteredPacket p Q iv boundary) (r : current.Earlier)
    (s : (current.predecessor r).Earlier) :
    (current.predecessor r).predecessor s =
      current.predecessor ⟨s.val, by
        have hs := s.property
        change position s.val < position r.val at hs
        exact hs.trans r.property⟩ := by
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply CanonicalPacket.messages_injective
  change (current.2.messages.drop (position current.2.coord - position r.val)).drop
    (position r.val - position s.val) =
      current.2.messages.drop (position current.2.coord - position s.val)
  rw [List.drop_drop]
  congr 1
  have hr := r.property
  have hs := s.property
  change position s.val < position r.val at hs
  omega

/-- The same global table links strict prefixes of adjacent (or any nested)
packets without chronology assumptions about the order of table queries. -/
theorem prefix_consistent (current : EnteredPacket p Q iv boundary) (r : current.Earlier)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary))
    (s : (current.predecessor r).Earlier) :
    rawPrefix (current.predecessor r) (fun k => table k.val) s.val s.property =
      rawPrefix current (fun k => table k.val) s.val (by
        have hs := s.property
        change position s.val < position r.val at hs
        exact hs.trans r.property) := by
  have hs := s.property
  change position s.val < position r.val at hs
  let readAt : {a : EnteredPacket p Q iv boundary // a.2.coord = s.val} → Raw s.val :=
    fun a => a.property ▸ grouped a.val.2.coord (table (.inl a.val))
  exact congrArg readAt
    (Subtype.ext (predecessor_comp current r s) :
      (⟨(current.predecessor r).predecessor s,rfl⟩ :
        {a : EnteredPacket p Q iv boundary // a.2.coord = s.val}) =
      ⟨current.predecessor ⟨s.val,hs.trans r.property⟩,rfl⟩)

/-- Source-history compatibility is explicit: a neighbouring packet in one
accepted history must be this literal predecessor, not just share a position.
Acceptance itself is not needed for this stronger functional equality. -/
theorem history_prefix_consistent (current previous : EnteredPacket p Q iv boundary)
    (r : current.Earlier) (history : previous = current.predecessor r)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary))
    (s : previous.Earlier) :
    ∃ _h : position s.val < position current.2.coord,
      get s.val (tape previous (fun k => table k.val)) =
        get s.val (tape current (fun k => table k.val)) := by
  subst previous
  have hs := s.property
  change position s.val < position r.val at hs
  refine ⟨hs.trans r.property, ?_⟩
  unfold tape
  rw [get_tapeOfPrefix _ s.property, get_tapeOfPrefix _ (hs.trans r.property)]
  exact congrArg (project s.val) (prefix_consistent current r table s)

theorem ring_table (current : EnteredPacket p Q iv boundary)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary))
    (h : position (.initial : Coordinate (ParameterBounds.config p)) < position current.2.coord) :
    ringPrefix current (fun k => table k.val) =
      (grouped .initial (table (.inl (current.predecessor ⟨.initial,h⟩)))).1 := by
  simp only [ringPrefix, ringOfPrefix, dite_eq_left h]
  rfl

open Classical in
theorem tape_update_current (current : EnteredPacket p Q iv boundary)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary))
    (full : Fin (blocks (rawWidth current.2.coord)) → Digest32) :
    tape current (fun k => Function.update table (.inl current) full k.val) =
      tape current (fun k => table k.val) :=
  reconstruction_update_current current (fun past => tapeOfPrefix (projectedPrefix past)) table full

open Classical in
theorem ring_update_current (current : EnteredPacket p Q iv boundary)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary))
    (full : Fin (blocks (rawWidth current.2.coord)) → Digest32) :
    ringPrefix current (fun k => Function.update table (.inl current) full k.val) =
      ringPrefix current (fun k => table k.val) :=
  reconstruction_update_current current ringOfPrefix table full

/-- Adjacent literal-history packets are linked by exactly one already assigned
Raw answer, not by resampling/warming a missing ancestor. -/
theorem adjacent_tape_step (current : EnteredPacket p Q iv boundary) (r : current.Earlier)
    (adjacent : position current.2.coord = position r.val + 1)
    (table : Table (p := p) (Q := Q) (iv := iv) (boundary := boundary)) :
    tape current (fun k => table k.val) =
      set r.val (tape (current.predecessor r) (fun k => table k.val))
        (project r.val (grouped r.val (table (.inl (current.predecessor r))))) := by
  apply (coordinates (ParameterBounds.config p)).injective
  funext s
  change get s _ = get s _
  by_cases same : s = r.val
  · subst s
    rw [get_set]
    exact get_table current table r
  · rw [get_set_ne _ _ _ _ same]
    by_cases earlier : position s < position r.val
    · have consistent := prefix_consistent current r table ⟨s,earlier⟩
      unfold tape
      rw [get_tapeOfPrefix (strictPrefix current (fun k => table k.val)) (earlier.trans r.property),
        get_tapeOfPrefix (strictPrefix (current.predecessor r) (fun k => table k.val)) earlier]
      exact congrArg (project s) consistent.symm
    · have distinct : position s ≠ position r.val :=
        fun h => same (CausalPrefix.position_injective _ h)
      have future : ¬ position s < position current.2.coord := by omega
      unfold tape
      rw [get_inert (strictPrefix current (fun k => table k.val)) future,
        get_inert (strictPrefix (current.predecessor r) (fun k => table k.val)) earlier]

#print axioms ring_table
#print axioms tape_update_current
#print axioms ring_update_current
#print axioms adjacent_tape_step
#print axioms get_table
#print axioms rawPrefix_bytes
#print axioms reconstruction_update_current
#print axioms predecessor_comp
#print axioms prefix_consistent
#print axioms history_prefix_consistent
#print axioms incoming_ignores_suffix
end Whir.PCSBCSSourcePacketTape
