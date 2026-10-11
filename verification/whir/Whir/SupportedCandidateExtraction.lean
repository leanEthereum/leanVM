import Whir.InitialCandidates
import Whir.KnowledgeExtraction

/-! Executable common-coordinate certification. Only supplied response records
are read; the ideal root is used in soundness statements, never in the checker.
The certificate is shared by every lane, including the zero-padded lanes. -/
namespace Whir.SupportedCandidateExtraction
open Concrete Protocol CausalGame CandidateFolding

abbrev width (c : Config) := 2 ^ (c.logN - c.folds[0]!)
abbrev laneCount (c : Config) := 2 ^ c.folds[0]!
abbrev blockLength (c : Config) := 2 ^ (c.logN - c.folds[0]! + c.rates[0]!)
abbrev Record (c : Config) := Fin (blockLength c) × Array K

/-- Occupied authenticated leaves have verifier order, opposite coefficient order. -/
def recordLane (lanes : Nat) (row : Array K) (l : Nat) : K :=
  if l < lanes then row[lanes - 1 - l]! else 0

/-- Cache each dense lane encoding once, independently of the record count. -/
def encodedLanes (c : Config) (candidate : Array E) : Array (Array E) :=
  Array.ofFn fun lane : Fin (laneCount c) =>
    encode (c.logN - c.folds[0]!) c.rates[0]!
      (Array.ofFn (unpack true (laneCount c) (width c) candidate lane))

/-- The dense source encoder, not a recomputed commitment, checks the certificate. -/
def rowMatches (c : Config) (lanes : Nat) (encoded : Array (Array E)) (record : Record c) : Bool :=
  record.2.size == lanes &&
    (List.finRange (laneCount c)).all (fun lane =>
      (encoded[lane.val]!)[record.1.val]! == E.ofK (recordLane lanes record.2 lane.val))

/-- Deduplicate coordinates, not rows: repeated queries cannot inflate support. -/
def commonCoordinates (c : Config) (lanes : Nat) (candidate : Array E)
    (records : List (Record c)) : Finset (Fin (blockLength c)) :=
  let encoded := encodedLanes c candidate
  ((records.filter (rowMatches c lanes encoded)).map Prod.fst).toFinset

def verified (input : Public) (candidate : Array E) (records : List (Record input.config)) : Bool :=
  candidate.size == laneCount input.config * width input.config &&
    decide (ParameterBounds.threshold input.config 0 ≤
      (commonCoordinates input.config input.lanes candidate records).card) &&
    input.claims.all (fun claim => dot candidate claim.weight == claim.value)

/-- Deterministic verified-output stop. No list membership or root-preimage test is evaluated. -/
def finish (input : Public) (candidate : Array E) (records : List (Record input.config)) :
    Option (Witness input.config input.lanes) :=
  if verified input candidate records then
    some (InitialCandidates.project input.config input.lanes candidate) else none

theorem matches_sound (c : Config) (lanes : Nat) (candidate : Array E) (record : Record c)
    (matched : rowMatches c lanes (encodedLanes c candidate) record = true) (lane : Fin (laneCount c)) :
    concreteEncoder (c.logN - c.folds[0]!) c.rates[0]!
      (unpack true (laneCount c) (width c) candidate lane) record.1 =
        E.ofK (recordLane lanes record.2 lane.val) := by
  have h : (List.finRange (laneCount c)).all (fun lane =>
      ((encodedLanes c candidate)[lane.val]!)[record.1.val]! ==
        E.ofK (recordLane lanes record.2 lane.val)) = true := by
    have h := matched
    simp only [rowMatches, Bool.and_eq_true] at h
    exact h.2
  have hrow := beq_iff_eq.mp (List.all_eq_true.mp h lane (List.mem_finRange lane))
  rw [ConcreteCandidates.concreteEncoder_ofFn]
  simpa [encodedLanes, getElem!_pos, lane.isLt] using hrow

/-- Authentication connects a finite output certificate to the commitment-only
mathematical list. Authentication must come from actual accepted verifier trials. -/
theorem verified_member (input : Public) (candidate : Array E)
    (records : List (Record input.config))
    (authenticated : ∀ record ∈ records, record.2 = input.root[record.1.val]!)
    (checked : verified input candidate records = true) :
    candidate ∈ InitialCandidates.extensionCandidates input.config input.lanes input.root := by
  obtain ⟨hshape, henough, _⟩ :
      candidate.size = laneCount input.config * width input.config ∧
      ParameterBounds.threshold input.config 0 ≤
        (commonCoordinates input.config input.lanes candidate records).card ∧
      input.claims.all (fun claim => dot candidate claim.weight == claim.value) = true := by
    simpa only [verified, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using checked
  apply (arrayCandidates_mem_iff _ _ _ _ _).mpr
  refine ⟨hshape, commonCoordinates input.config input.lanes candidate records, henough, ?_⟩
  intro lane q hq
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  obtain ⟨member, matched⟩ := List.mem_filter.mp hrecord
  have equality := matches_sound input.config input.lanes candidate record matched lane
  rw [authenticated record member] at equality
  exact equality

/-- Literal K reconstruction preserves the very candidate checked by the stop rule. -/
theorem finish_explains (input : Public) (candidate : Array E)
    (records : List (Record input.config))
    (authenticated : ∀ record ∈ records, record.2 = input.root[record.1.val]!)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (laneBound : input.lanes ≤ laneCount input.config)
    (depth : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (threshold : width input.config - 1 < ParameterBounds.threshold input.config 0)
    (w : Witness input.config input.lanes)
    (output : finish input candidate records = some w) :
    KnowledgeExtraction.Explains input w := by
  unfold finish at output
  split at output
  · rename_i checked
    have equal := Option.some.inj output
    subst w
    have member := verified_member input candidate records authenticated checked
    refine ⟨Finset.mem_image.mpr ⟨candidate, member, rfl⟩, ?_⟩
    have reconstructed := InitialCandidates.reconstruction input.config input.lanes input.root
      foldBound laneBound depth threshold candidate member
    have claims : input.claims.all (fun claim => dot candidate claim.weight == claim.value) = true := by
      have h := checked
      simp only [verified, Bool.and_eq_true] at h
      exact h.2
    intro claim memberClaim
    rw [← reconstructed]
    have hc := List.all_eq_true.mp (show input.claims.toList.all
      (fun claim => dot candidate claim.weight == claim.value) = true by
        simpa using claims) claim memberClaim
    exact beq_iff_eq.mp hc
  · contradiction

#print axioms verified_member
#print axioms finish_explains
end Whir.SupportedCandidateExtraction
