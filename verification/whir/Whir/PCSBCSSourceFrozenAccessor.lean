import Whir.PCSBCSSourceRootReferences
import Whir.PCSBCSFrozenOracleRows
import Whir.PCSBCSSourcePacketTape
import Whir.PCSBCSSourceReplyInversion

/-! Checked source access, not authentication. The registry is captured under
its four-field Reference by the parent. Unavailable captured cells remain ghost
zeros with explicit status; a missing capture is never totalized into a root.
Remaining integration hypotheses, exactly:
* the saved Record is the immutable caller binding and config is the source config;
* each supplied capture is frozen at its actual first shape-address mention, with
  CV binding to that Reference and actual ordinary primitive-prefix provenance;
* Pending metadata is the admitted SourcePacket prefix and the supplied Prefix
  is reconstructed from its literal strict predecessor source-packet answers;
* accepted opening transport implies the selected captured rows/path relation
  outside OpeningBad; unavailable zeros and valid padding alone do NOT imply it;
* equality to an unnormalized semantic reply additionally requires the existing
  canonicalReply compatibility hypothesis (scalar equality proves only quotient
  equality). Physical-log identification remains the parent's coupling task.
No final security bound, all-leaf availability or Fiat-Shamir endpoint is assumed.
Only fields read by decodeReplyScalars are supplied to its established inverse. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceFrozenAccessor
open Concrete Protocol CausalGame CausalProbability WHIRHistory FiatShamirGame
open AnchoredHeaderCodec PCSBCSMerkleRootCache PCSBCSMerkleLeafImages
open PCSBCSSourceRootReferences PCSBCSSourceReplyInversion

abbrev Captures := Reference → Option Frozen

def sameShape (a b : PCSBCSMerkleRootCache.Shape) : Bool :=
  a.height == b.height && a.leafWords == b.leafWords && a.occupied == b.occupied

/-- Check saved storage without silently repairing a corrupted image or table.
Bad padding is represented faithfully here, including in unqueried next rows. -/
def cellValid (s : PCSBCSMerkleRootCache.Shape) (cell : ImageCell) : Bool := Id.run do
  if s.occupied > s.leafWords || cell.image.size != s.leafWords ||
      cell.compact.size != s.occupied then return false
  let padding := s.leafWords-s.occupied
  for n in [:s.occupied] do
    if cell.compact[n]! != cell.image[padding+n]! then return false
  if cell.available then
    let mut valid := true
    for n in [:padding] do
      if cell.image[n]! != 0 then
        valid := false
        break
    return cell.paddingValid == valid
  else
    return cell.image.all (· == 0) && !cell.paddingValid

def structurallyValid (ref : Reference) (f : Frozen) : Bool :=
  sameShape f.shape ref.shape && decide (ref.shape.occupied ≤ ref.shape.leafWords) &&
  f.cells.size == 2^ref.shape.height && f.raw.size == f.cells.size &&
  (Id.run do
    for n in [:f.cells.size] do
      match f.cells[n]? with
      | none => return false
      | some cell =>
        if !(cellValid ref.shape cell && f.raw[n]? == some cell.compact) then return false
    return true)

def lookup (registry : Captures) (ref : Reference) : Option Frozen := do
  let f ← registry ref
  if structurallyValid ref f then some f else none

/-- The saved initial frame and literal scheduled phase-root roles are reused;
no search for equal digest values or arbitrary scalar offsets occurs. -/
def phaseReference (c : Config) (saved : Record) (messages : List Pending)
    (phase : Nat) : Option Reference :=
  if phase = 0 then
    if saved.shape.logN = c.logN ∧ saved.shape.logBatch = c.folds[0]! ∧
        saved.shape.logRate = c.rates[0]! then
      parseInitial saved (openingScalars saved) 3
    else none
  else if phaseRolesAdmitted c messages then do
    let ref ← (phaseReferences c messages)[phase-1]?
    if sameShape ref.shape (phaseShape c phase) then some ref else none
  else none

structure Status where
  available : Bool
  paddingValid : Bool
  deriving BEq, Repr, Inhabited

def status (cell : ImageCell) : Status := ⟨cell.available,cell.paddingValid⟩

structure Selected where
  queries : Array Nat
  rows : Oracle
  cells : Array ImageCell

/-- Checked traversal keeps duplicates in exactly the derived order. A captured
unavailable cell is admissible ghost data, but available nonzero padding rejects.
Its availability remains explicit and cannot be used as authenticity evidence. -/
def selectPhase (phase : Nat) (f : Frozen) (queries : Array Nat) : Option Selected := do
  let oracle ← PCSBCSFrozenOracleRows.frozenOracle phase f
  let rows ← PCSBCSFrozenOracleRows.queryRows oracle queries
  let cells ← queries.mapM (fun n => f.cells[n]?)
  if cells.all (fun cell => !cell.available || cell.paddingValid) then
    some ⟨queries,rows,cells⟩
  else none

structure Access where
  rows : Oracle := #[]
  next : Oracle := #[]
  queries : Array Nat := #[]
  selectedStatus : Array Status := #[]
  nextStatus : Array Status := #[]

def oracles {c : Config} (a : Access) : FrozenOracles c :=
  ⟨fun _ => a.rows,fun _ _ => a.next⟩

/-- Construction is per strict earlier coordinate. Unused decoder branches are
inert; no decoder branch needing a capture can reach those inert values. -/
def build {c : Config} (current : Coordinate c) (saved : Record)
    (registry : Captures) (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (q : Coordinate c) (m : Pending) : Option Access :=
  if earlier : position q < position current then
    match q with
    | .query i => do
      let priorMessages := (messages.reverse.take (position (.query i : Coordinate c)+1)).reverse
      let ref ← phaseReference c saved priorMessages i.val
      let f ← lookup registry ref
      let raw := past (.query i) earlier
      let queries ← deriveQueries (remaining c i.val+c.rates[i.val]!) c.queries[i.val]!
        (Array.ofFn raw.1)
      let selected ← selectPhase i.val f queries
      pure ⟨selected.rows,#[],queries,selected.cells.map status,#[]⟩
    | .fold i j =>
      if j.val+1 = c.folds[i.val]! ∧ i.val+1 < c.folds.size then do
        let ref ← parsePhase c (.fold i j) m (i.val+1) 2
        let f ← lookup registry ref
        let next ← PCSBCSFrozenOracleRows.frozenOracle (i.val+1) f
        pure ⟨#[],next,#[],#[],f.cells.map status⟩
      else some {}
    | _ => some {}
  else none

/-- Each needed partial lookup is validated BEFORE the total inverse is called. -/
def inverseAt {c : Config} (current : Coordinate c) (saved : Record)
    (registry : Captures) (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (n : Nat) : Option Inverted := do
  let q ← (schedule c)[n]?
  let m ← messages.reverse[n+1]?
  let a ← build current saved registry messages past q m
  inverse (oracles a) q (stage q) m

/-- Actual SourcePacket Pending prefixes are used unchanged. -/
def packetInverseAt {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {entry : FramedHistory} {current : Coordinate (ParameterBounds.config p)}
    (packet : PCSBCSChallengeOracle.SourcePacket p Q iv entry current)
    (saved : Record) (registry : Captures) (past : WHIRFiatShamir.Prefix current)
    (n : Nat) : Option Inverted :=
  inverseAt current saved registry packet.messages past n

 theorem lookup_missing (registry : Captures) (ref : Reference)
    (missing : registry ref = none) : lookup registry ref = none := by
  simp [lookup,missing]

 theorem lookup_malformed (registry : Captures) (ref : Reference) (f : Frozen)
    (captured : registry ref = some f) (bad : structurallyValid ref f = false) :
    lookup registry ref = none := by simp [lookup,captured,bad]

 theorem build_not_earlier {c : Config} (current q : Coordinate c) (saved : Record)
    (registry : Captures) (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (m : Pending) (late : ¬ position q < position current) :
    build current saved registry messages past q m = none := by simp [build,late]

 theorem selectPhase_order (phase : Nat) (f : Frozen) (qs : Array Nat) (s : Selected)
    (selected : selectPhase phase f qs = some s) :
    s.queries = qs ∧ ∃ oracle,
      PCSBCSFrozenOracleRows.frozenOracle phase f = some oracle ∧
      s.rows.size = qs.size ∧
      ∀ i : Fin qs.size, s.rows[i.val]! = oracle[qs[i]]! := by
  unfold selectPhase at selected
  cases ho : PCSBCSFrozenOracleRows.frozenOracle phase f with
  | none => simp [ho] at selected
  | some oracle =>
    simp only [ho] at selected
    dsimp only [Bind.bind,Option.bind] at selected
    cases hr : PCSBCSFrozenOracleRows.queryRows oracle qs with
    | none => simp [hr] at selected
    | some rows =>
      simp only [hr] at selected
      cases hc : qs.mapM (fun n => f.cells[n]?) with
      | none => simp [hc] at selected
      | some cells =>
        simp only [hc] at selected
        change (if cells.all (fun cell => !cell.available || cell.paddingValid) then
          some (⟨qs,rows,cells⟩ : Selected) else none) = some s at selected
        split at selected
        next =>
          cases Option.some.inj selected
          exact ⟨rfl,oracle,rfl,PCSBCSFrozenOracleRows.queryRows_spec oracle rows qs hr⟩
        next => contradiction

 theorem selectPhase_bad_index (phase : Nat) (f : Frozen) (qs : Array Nat)
    (bad : qs.mapM (fun n => f.cells[n]?) = none) : selectPhase phase f qs = none := by
  unfold selectPhase
  cases PCSBCSFrozenOracleRows.frozenOracle phase f <;> dsimp only [Bind.bind,Option.bind]
  case some oracle =>
    cases PCSBCSFrozenOracleRows.queryRows oracle qs <;> simp [bad]

 theorem inverseAt_integration {c : Config} (current : Coordinate c) (saved : Record)
    (registry : Captures) (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (n : Nat) (q : Coordinate c) (m : Pending) (a : Access)
    (coordinate : (schedule c)[n]? = some q) (message : messages.reverse[n+1]? = some m)
    (constructed : build current saved registry messages past q m = some a) :
    inverseAt current saved registry messages past n = inverse (oracles a) q (stage q) m := by
  simp [inverseAt,coordinate,message,constructed]

/-- Whole current answers can change arbitrarily: the constructor receives only
captured registry, immutable Pending metadata and the strict predecessor prefix. -/
 theorem whole_current_invariance {c : Config} (current : Coordinate c) (saved : Record)
    (left right : Captures) (messages : List Pending)
    (past future : WHIRFiatShamir.Prefix current) (n : Nat)
    (registrySame : left = right) (prefixSame : ∀ q h, past q h = future q h) :
    inverseAt current saved left messages past n = inverseAt current saved right messages future n := by
  have same : past = future := by funext q h; exact prefixSame q h
  rw [registrySame,same]

 theorem selectPhase_bad_padding (phase : Nat) (f : Frozen) (qs : Array Nat)
    (cells : Array ImageCell) (selected : qs.mapM (fun n => f.cells[n]?) = some cells)
    (bad : cells.all (fun cell => !cell.available || cell.paddingValid) = false) :
    selectPhase phase f qs = none := by
  unfold selectPhase
  cases PCSBCSFrozenOracleRows.frozenOracle phase f <;> dsimp only [Bind.bind,Option.bind]
  case some oracle =>
    cases PCSBCSFrozenOracleRows.queryRows oracle qs <;> dsimp only [Bind.bind,Option.bind]
    case some rows =>
      rw [selected]
      change (if cells.all (fun cell => !cell.available || cell.paddingValid) then
        some (⟨qs,rows,cells⟩ : Selected) else none) = none
      rw [bad]
      rfl

open Classical in
/-- Literal whole-packet replacement, including unused bytes, specializes the
strict-tape reconstruction theorem with the fixed captured registry. -/
theorem inverseAt_update_current {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32}
    {boundary : Nat} (current : PCSBCSChallengeOracle.EnteredPacket p Q iv boundary)
    (saved : Record) (registry : Captures) (n : Nat)
    (table : PCSBCSSourcePacketTape.Table (p := p) (Q := Q) (iv := iv) (boundary := boundary))
    (full : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth current.2.coord)) → Digest32) :
    inverseAt current.2.coord saved registry current.2.messages
      (PCSBCSSourcePacketTape.strictPrefix current
        (fun k => Function.update table (.inl current) full k.val)) n =
    inverseAt current.2.coord saved registry current.2.messages
      (PCSBCSSourcePacketTape.strictPrefix current (fun k => table k.val)) n := by
  exact PCSBCSSourcePacketTape.reconstruction_update_current current
    (fun past => inverseAt current.2.coord saved registry current.2.messages
      (PCSBCSSourcePacketTape.projectedPrefix past) n) table full

theorem build_query {c : Config} (current : Coordinate c) (saved : Record)
    (registry : Captures) (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (i : Fin c.folds.size) (m : Pending)
    (earlier : position (.query i : Coordinate c) < position current)
    (ref : Reference) (f : Frozen) (qs : Array Nat) (s : Selected)
    (reference : phaseReference c saved
      (messages.reverse.take (position (.query i : Coordinate c)+1)).reverse i.val = some ref)
    (captured : lookup registry ref = some f)
    (derived : deriveQueries (remaining c i.val+c.rates[i.val]!) c.queries[i.val]!
      (Array.ofFn (past (.query i) earlier).1) = some qs)
    (selected : selectPhase i.val f qs = some s) :
    build current saved registry messages past (.query i) m =
      some ⟨s.rows,#[],qs,s.cells.map status,#[]⟩ := by
  simp [build,earlier,reference,captured,derived,selected]

theorem build_fold_next {c : Config} (current : Coordinate c) (saved : Record)
    (registry : Captures) (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (i : Fin c.folds.size) (j : Fin c.folds[i.val]!) (m : Pending)
    (earlier : position (.fold i j : Coordinate c) < position current)
    (last : j.val+1 = c.folds[i.val]!) (later : i.val+1 < c.folds.size)
    (ref : Reference) (f : Frozen) (next : Oracle)
    (reference : parsePhase c (.fold i j) m (i.val+1) 2 = some ref)
    (captured : lookup registry ref = some f)
    (decoded : PCSBCSFrozenOracleRows.frozenOracle (i.val+1) f = some next) :
    build current saved registry messages past (.fold i j) m =
      some ⟨#[],next,#[],#[],f.cells.map status⟩ := by
  simp [build,earlier,last,later,reference,captured,decoded]

theorem inverseAt_late {c : Config} (current q : Coordinate c) (saved : Record)
    (registry : Captures) (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (n : Nat) (coordinate : (schedule c)[n]? = some q)
    (late : ¬ position q < position current) :
    inverseAt current saved registry messages past n = none := by
  unfold inverseAt
  rw [coordinate]
  cases messages.reverse[n+1]? <;> simp [build,late]

#print axioms lookup_missing
#print axioms lookup_malformed
#print axioms build_not_earlier
#print axioms selectPhase_order
#print axioms selectPhase_bad_index
#print axioms inverseAt_integration
#print axioms whole_current_invariance
#print axioms selectPhase_bad_padding
#print axioms inverseAt_update_current
#print axioms build_query
#print axioms build_fold_next
#print axioms inverseAt_late
end Whir.PCSBCSSourceFrozenAccessor
