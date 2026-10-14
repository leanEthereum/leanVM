import Whir.PCSBCSSourceCallerSnapshot
import Whir.PCSBCSSourceFrozenAccessorStructural
import Whir.PCSBCSMerkleRootCacheTransport
import Whir.PCSBCSSourcePrimitiveRootBudget

/-! Literal root-address and strict-prefix transport for the captured source
builder. Shape admission is not authentication; authenticated full padded
openings, rather than unavailable default cells, supply opening transport. -/
set_option autoImplicit false
namespace Whir.PCSBCSCapturedSourceTransport
open Concrete Protocol CausalGame CausalProbability FiatShamirGame WHIRHistory
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSMerkleRootCache
open PCSBCSSourceCallerSnapshot PCSBCSSourceReplyInversion
open TypedOracleCompiler TypedFiatShamirGame
open PCSStateRestoration.Latent

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- The address reads only the literal construction entry and Pending bytes.
Unqueried caller answers cannot decide whether an earlier prequery mentions a
root. Primitive-query keys do not announce source roots. -/
def address : Keys → List Reference
  | .inl packet => (PCSBCSSourcePrimitiveRootBudget.openingReferencesFromEntry p packet.1.val
      (WHIRCallerPrefix.outputKeyFrom (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
        packet.1.val packet.2.messages 0)).getD []
  | .inr _ => []

/-- Once the literal caller parser admits the immutable binding, its exact
root roles are the initial root followed by the scheduled prior fold roots. -/
theorem address_packet (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (answers : FiatShamirGame.Coordinate → Digest32)
    (current : EnteredPacket p Q iv boundary)
    (valid : saved.Valid) (profile : profileShape p saved.shape)
    (claims : AnchoredSourceCaller.Claims)
    (caller : AnchoredSourceFreshCaller.decode layout saved current.1.val answers = some claims)
    (roles : phaseRolesAdmitted (ParameterBounds.config p) current.2.messages = true) :
    address (.inl current) =
      ⟨saved.root,initialShape saved.shape⟩ :: phaseReferences (ParameterBounds.config p) current.2.messages := by
  have parsed := parsePendingKey_roundtrip p current.1.val current.2.messages
    current.2.2.nonempty current.2.2.admitted 0
  have semantic : parseReferences p layout saved current.1.val answers
      (WHIRCallerPrefix.outputKeyFrom (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
        current.1.val current.2.messages 0) =
      some (⟨saved.root,initialShape saved.shape⟩ :: phaseReferences (ParameterBounds.config p) current.2.messages) := by
    simp [parseReferences,valid,profile,caller,parsed,roles]
  have admission := PCSBCSSourcePrimitiveRootBudget.openingReferencesFromEntry_native p layout saved answers
    current.1.val _ _ semantic
  simp only [address,admission,Option.getD_some]

/-- Root roles in any literal chronological prefix also occur in the current
packet. This is address membership, not a promise that the root is available. -/
theorem phaseReferences_prefix (c : Config) (messages : List Pending) (count : Nat)
    (ref : Reference)
    (member : ref ∈ phaseReferences c (messages.reverse.take count).reverse) :
    ref ∈ phaseReferences c messages := by
  obtain ⟨⟨m,n⟩,inside,parsed⟩ := List.mem_filterMap.mp member
  simp only [List.reverse_reverse] at inside
  have indexed := List.mk_mem_zipIdx_iff_getElem?.mp inside
  have original : messages.reverse[n]? = some m := by
    have bound : n < count := by
      have h := List.getElem?_eq_some_iff.mp indexed
      have length : n < (messages.reverse.take count).length := h.1
      simp only [List.length_take] at length
      omega
    simpa only [List.getElem?_take,bound,↓reduceIte] using indexed
  exact List.mem_filterMap.mpr ⟨(m,n),List.mk_mem_zipIdx_iff_getElem?.mpr original,parsed⟩

/-- The accessor's checked phase role necessarily belongs to the literal
current root-role list; future roots cannot enter via a suffix search. -/
theorem phaseReference_member (c : Config) (saved : AnchoredHeaderCodec.Record)
    (messages : List Pending) (phase count : Nat) (ref : Reference)
    (parsed : PCSBCSSourceFrozenAccessor.phaseReference c saved
      (messages.reverse.take count).reverse phase = some ref) :
    ref ∈ ⟨saved.root,initialShape saved.shape⟩ :: phaseReferences c messages := by
  unfold PCSBCSSourceFrozenAccessor.phaseReference at parsed
  split at parsed
  next initial =>
    split at parsed
    next =>
      have equal := (parseInitial_admitted saved (AnchoredHeaderCodec.openingScalars saved) 3 ref parsed).2.2.2
      simp only [equal,List.mem_cons, true_or]
    next => contradiction
  next =>
    split at parsed
    next =>
      obtain ⟨found,indexed,continued⟩ := Option.bind_eq_some_iff.mp parsed
      split at continued
      next =>
        cases Option.some.inj continued
        exact List.mem_cons_of_mem _ (phaseReferences_prefix c messages count ref (List.mem_of_getElem? indexed))
      next => contradiction
    next => contradiction

/-- A next root announced by a literal final nonterminal fold is already
addressed by the current Pending history, at its exact scheduled index. -/
theorem foldReference_member (c : Config) (messages : List Pending) (n : Nat)
    (i : Fin c.folds.size) (j : Fin c.folds[i.val]!) (m : Pending) (ref : Reference)
    (coordinate : (schedule c)[n]? = some (.fold i j))
    (message : messages.reverse[n+1]? = some m)
    (parsed : parsePhase c (.fold i j) m (i.val+1) 2 = some ref) :
    ref ∈ phaseReferences c messages := by
  apply List.mem_filterMap.mpr
  refine ⟨(m,n+1),List.mk_mem_zipIdx_iff_getElem?.mpr message,?_⟩
  change phaseAt c (n+1) m = some ref
  simpa only [phaseAt,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,
    Nat.add_sub_cancel,coordinate,Option.getD_some] using parsed

/-- Every enabled, actually visited root has a first-disclosure capture. The
constructor does not demand that unqueried leaves be physically available. -/
theorem registry_exists {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R n)
    (table : Table Keys Answers) (current : EnteredPacket p Q iv boundary)
    (ref : Reference) (mentioned : ref ∈ addresses (.inl current))
    (visited : (.inl current : Keys) ∈ ((Sampling.execute table program).2.map Sigma.fst)) :
    ∃ frozen, capturedRegistry addresses program current (fun key => table key.val) ref = some frozen := by
  obtain ⟨frozen,captured⟩ := PCSBCSSourceRootCapture.capture_exists addresses ref
    (.inl current) mentioned program table visited
  exact ⟨frozen,by rw [capturedRegistry_enabled addresses program current table ref mentioned]; exact captured⟩

/-- Enabled visited roots pass the actual storage checks because capture is a
literal freeze, not because of an assumed valid registry or honest root. -/
theorem lookup_exists {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R n)
    (table : Table Keys Answers) (current : EnteredPacket p Q iv boundary)
    (ref : Reference) (mentioned : ref ∈ addresses (.inl current))
    (fits : ref.shape.occupied ≤ ref.shape.leafWords)
    (visited : (.inl current : Keys) ∈ ((Sampling.execute table program).2.map Sigma.fst)) :
    ∃ frozen, PCSBCSSourceFrozenAccessor.lookup
      (capturedRegistry addresses program current (fun key => table key.val)) ref = some frozen ∧
      PCSBCSSourceRootCapture.capture addresses ref program table = some frozen := by
  obtain ⟨frozen,captured⟩ := PCSBCSSourceRootCapture.capture_exists addresses ref
    (.inl current) mentioned program table visited
  obtain ⟨events,_,equal,_⟩ := PCSBCSSourceRootCapture.capture_provenance
    addresses ref program table frozen captured
  refine ⟨frozen,?_,captured⟩
  rw [equal]
  apply PCSBCSSourceFrozenAccessorStructural.lookup_freeze _ _ ref fits
  rw [capturedRegistry_enabled addresses program current table ref mentioned,captured,equal]

/-- Completeness of the real forward builder follows from individual checked
inverse successes, not from a supplied whole-prefix work certificate. -/
theorem collect_complete {c : Config} (current : Coordinate c)
    (saved : AnchoredHeaderCodec.Record) (registry : PCSBCSSourceFrozenAccessor.Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (stages : Array (Coordinate c)) (chronological : Array Pending) (count start : Nat)
    (out : Array Reply)
    (available : ∀ j, j < count → ∃ reply,
      PCSBCSSourceFrozenReplies.inverseIndexed current saved registry messages past stages chronological (start+j) = some reply) :
    ∃ result, PCSBCSSourceFrozenReplies.collect current saved registry messages past
      stages chronological count start out = some result := by
  induction count generalizing start out with
  | zero => exact ⟨out,rfl⟩
  | succ count ih =>
    obtain ⟨reply,parsed⟩ := available 0 (by omega)
    simp only [Nat.add_zero] at parsed
    obtain ⟨result,rest⟩ := ih (start+1) (out.push reply.reply) (by
      intro j earlier
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using available (j+1) (by omega))
    exact ⟨result,by simp only [PCSBCSSourceFrozenReplies.collect,parsed]; exact rest⟩

/-- Full padded source openings either agree with the actual captured suffix
and prove both status bits, or exhibit the existing ordinary primitive bad
event. No completeness or leaf-availability promise replaces this dichotomy. -/
theorem captured_opening {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R n)
    (table : Table Keys Answers) (ref : Reference) (f : Frozen)
    (captured : PCSBCSSourceRootCapture.capture addresses ref program table = some f)
    (C : DuplexModeGame.PrimitiveOracle) (proof : MerkleTransport.PrunedMerklePaths)
    (numLeaves : Nat) (queries : List Nat) (output : List MerkleTransport.RawPath)
    (height : ref.shape.height = numLeaves.log2)
    (auth : PublicMerkleLog.AuthenticLog C f.queryPrefix)
    (accepted : PCSBCSMerkleFullSourceTransport.openSource (PublicMerkleLog.hash C)
      proof ref.root numLeaves queries ref.shape.leafWords ref.shape.occupied = some output)
    (bounds : ∀ path ∈ output, ∀ bytes ∈
      path.opening.inputs (MerkleTransport.hashing (PublicMerkleLog.hash C)), bytes.length < 2^64) :
    List.Forall₂ (fun q path => f.raw[q]! =
      (path.leafData.drop (ref.shape.leafWords-ref.shape.occupied)).toArray ∧
      (f.cells[q]?).map (fun cell => (cell.available,cell.paddingValid)) = some (true,true))
      queries output ∨ PublicMerkleBinding.OpenPrimitiveBad C f.queryPrefix ref.root output := by
  obtain ⟨events,_,frozen,_⟩ := PCSBCSSourceRootCapture.capture_provenance
    addresses ref program table f captured
  obtain ⟨compact,_,opened⟩ := PCSBCSMerkleFullSourceTransport.openSource_refines
    (PublicMerkleLog.hash C) proof ref.root numLeaves queries ref.shape.leafWords
    ref.shape.occupied output accepted
  have rows := PCSBCSMerkleSourceRows.pruned_opened_compact C f.queryPrefix auth ref.root
    compact numLeaves ref.shape.leafWords ref.shape.occupied queries output opened bounds
  rw [frozen] at rows ⊢
  simpa only [freeze,height] using rows

/-- The actual successful inverse determines the exact strict answer array,
including all repeated query indexes. -/
theorem replies_complete {c : Config} (current : Coordinate c)
    (saved : AnchoredHeaderCodec.Record) (registry : PCSBCSSourceFrozenAccessor.Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (available : ∀ j, j < position current → ∃ reply,
      PCSBCSSourceFrozenAccessor.inverseAt current saved registry messages past j = some reply) :
    ∃ result, PCSBCSSourceFrozenReplies.replies current saved registry messages past = some result := by
  apply collect_complete
  intro j earlier
  simpa only [Nat.zero_add,PCSBCSSourceFrozenReplies.inverseIndexed_eq] using available j earlier

/-- Once actual checked earlier inverses succeed, the visited initial-root
address gives a successful captured caller snapshot. -/
theorem fromCapture_complete {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R n)
    (table : Table Keys Answers) (current : EnteredPacket p Q iv boundary)
    (ref : Reference) (input : PCSBCSCallerBinding.CallerInput p)
    (saved : AnchoredHeaderCodec.Record) (mentioned : ref ∈ addresses (.inl current))
    (visited : (.inl current : Keys) ∈ ((Sampling.execute table program).2.map Sigma.fst))
    (available : ∀ j, j < position current.2.coord → ∃ reply,
      PCSBCSSourceFrozenAccessor.inverseAt current.2.coord saved
        (capturedRegistry addresses program current (fun key => table key.val))
        current.2.messages (PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val)) j = some reply) :
    ∃ data, fromCapture addresses ref program input saved current (fun key => table key.val) = some data := by
  obtain ⟨root,captured⟩ := registry_exists addresses program table current ref mentioned visited
  obtain ⟨answers,parsed⟩ := replies_complete current.2.coord saved
    (capturedRegistry addresses program current (fun key => table key.val)) current.2.messages
    (PCSBCSSourcePacketTape.strictPrefix current (fun key => table key.val)) available
  exact ⟨⟨input,PCSBCSRestorationHazard.incomingData p root.raw
      (PCSBCSSourcePacketTape.ringPrefix current (fun key => table key.val))
      (PCSBCSSourcePacketTape.tape current (fun key => table key.val)) answers current.2.coord⟩,by
    simp only [fromCapture,captured,parsed]; rfl⟩

#print axioms address_packet
#print axioms phaseReferences_prefix
#print axioms phaseReference_member
#print axioms registry_exists
#print axioms collect_complete
#print axioms captured_opening
#print axioms replies_complete
#print axioms fromCapture_complete
#print axioms foldReference_member
#print axioms lookup_exists
end Whir.PCSBCSCapturedSourceTransport
