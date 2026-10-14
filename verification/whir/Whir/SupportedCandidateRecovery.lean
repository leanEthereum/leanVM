import Whir.PCSRewindExtractor
import Whir.UniqueRadiusSampling

/-! Deterministic recovery from authenticated heavy coordinates. All records are
retained, including accepted records outside the heavy agreement set. Such
coordinates may be erroneous; the radius charges their entire complement. -/
namespace Whir.SupportedCandidateRecovery
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open PCSRewindExtractor

set_option maxHeartbeats 2000000

/-- The occupied lane in the padded table is exactly the Gao decoder's input
coefficient ordering; there is no reversal or extension projection shortcut. -/
theorem encodedLane_witness (input : Public)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (laneBound : input.lanes ≤ laneCount input.config)
    (w : Witness input.config input.lanes) (lane : Fin input.lanes) :
    (encodedLanes input.config (paddedWitness input.config input.lanes w))[lane.val]! =
      encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
        ((PCSRewindExtraction.witnessLane input w lane).map E.ofK) := by
  have live : lane.val < laneCount input.config := lane.isLt.trans_le laneBound
  simp only [encodedLanes, getElem!_pos, Array.size_ofFn, live, Array.getElem_ofFn]
  congr 1
  apply Array.ext
  · simp [PCSRewindExtraction.witnessLane, PCSRewindExtraction.rowWidth]
  · intro j hj hk
    have jBound : j < width input.config := by simpa using hj
    have occupied : lane.val * width input.config + j < input.lanes * width input.config :=
      (Nat.add_lt_add_left jBound _).trans_le (by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ lane.isLt)
    have full : lane.val * width input.config + j < 2 ^ input.config.logN := by
      have bound := Nat.mul_le_mul_right (width input.config) laneBound
      have size : laneCount input.config * width input.config = 2 ^ input.config.logN := by
        rw [← Nat.pow_add, Nat.add_sub_of_le foldBound]
      exact occupied.trans_le (size ▸ bound)
    simp only [Array.getElem_ofFn, Array.getElem_map,
      PCSRewindExtraction.witnessLane, PCSRewindExtraction.rowWidth]
    change (paddedWitness input.config input.lanes w)[j + width input.config * lane.val]! =
      E.ofK (w ⟨lane.val * width input.config + j, occupied⟩)
    have index : j + width input.config * lane.val = lane.val * width input.config + j := by
      rw [Nat.mul_comm]; omega
    rw [index]
    unfold paddedWitness
    rw [ArrayLayout.getElem!_tab _ _ _ full]
    simp [occupied]

/-- A full common-coordinate check entails agreement for each live Gao lane. -/
theorem live_agrees_of_rowMatches (input : Public)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (laneBound : input.lanes ≤ laneCount input.config)
    (w : Witness input.config input.lanes) (q : Fin (blockLength input.config))
    (matched : rowMatches input.config input.lanes
      (encodedLanes input.config (paddedWitness input.config input.lanes w))
      (q, input.root[q.val]!) = true) (lane : Fin input.lanes) :
    E.ofK (recordLane input.lanes input.root[q.val]! lane.val) =
      (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
        ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]! := by
  have all : (List.finRange (laneCount input.config)).all (fun l =>
      ((encodedLanes input.config (paddedWitness input.config input.lanes w))[l.val]!)[q.val]! ==
        E.ofK (recordLane input.lanes input.root[q.val]! l.val)) = true := by
    have guard := matched
    simp only [rowMatches, Bool.and_eq_true] at guard
    exact guard.2
  have equal := beq_iff_eq.mp (List.all_eq_true.mp all
    ⟨lane.val, lane.isLt.trans_le laneBound⟩ (List.mem_finRange _))
  rw [encodedLane_witness input foldBound laneBound w lane] at equal
  exact equal.symm

/-- A covered authenticated coordinate is read from the actual record lookup. -/
theorem receivedLane_at_covered (input : Public) (records : List (Record input.config))
    (authenticated : ∀ record ∈ records, record.2 = input.root[record.1.val]!)
    (q : Fin (blockLength input.config))
    (covered : ∃ record ∈ records, record.1 = q) (lane : Fin input.lanes) :
    receivedLane input records lane q = E.ofK (recordLane input.lanes input.root[q.val]! lane.val) := by
  have found := RewindRowExtraction.lookup_authenticated records
    (fun q => input.root[q.val]!) authenticated q covered
  simp [receivedLane, receivedLaneCached, filledRecords, getElem!_pos, q.isLt, found]

/-- Missing observations are explicitly zero-filled, not obtained from a
root preimage or from an out-of-bounds access to a fabricated empty leaf. -/
theorem receivedLane_at_missing (input : Public) (records : List (Record input.config))
    (q : Fin (blockLength input.config)) (missing : RewindRowExtraction.lookup records q = none)
    (lane : Fin input.lanes) : receivedLane input records lane q = 0 := by
  simp [receivedLane, receivedLaneCached, filledRecords, getElem!_pos, q.isLt, missing]

/-- No honesty is claimed away from H, even for other authenticated records. -/
theorem receivedLane_distance (input : Public) (records : List (Record input.config))
    (authenticated : ∀ record ∈ records, record.2 = input.root[record.1.val]!)
    (H : Finset (Fin (blockLength input.config)))
    (covered : ∀ q ∈ H, ∃ record ∈ records, record.1 = q)
    (w : Witness input.config input.lanes)
    (agrees : ∀ q ∈ H, ∀ lane : Fin input.lanes,
      E.ofK (recordLane input.lanes input.root[q.val]! lane.val) =
        (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
          ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]!)
    (lane : Fin input.lanes) :
    hammingDist (receivedLane input records lane)
      (fun q => (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
        ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]!) ≤
      blockLength input.config - H.card := by
  classical
  let target := fun q : Fin (blockLength input.config) =>
    (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
      ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]!
  have subset : H ⊆ UniqueRadiusSampling.agreement
      (input.config.logN - input.config.folds[0]! + input.config.rates[0]!)
      (receivedLane input records lane) target := by
    intro q member
    simp only [UniqueRadiusSampling.agreement, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (receivedLane_at_covered input records authenticated q (covered q member) lane).trans
      (agrees q member lane)
  have card := Finset.card_le_card subset
  have partition := UniqueRadiusSampling.agreement_add_distance
    (input.config.logN - input.config.folds[0]! + input.config.rates[0]!)
    (receivedLane input records lane) target
  change hammingDist (receivedLane input records lane) target ≤
    blockLength input.config - H.card
  change _ + hammingDist (receivedLane input records lane) target =
    blockLength input.config at partition
  omega

private theorem hammingDist_index_cast {M N : Nat} (same : M = N) (received target : Fin N → E) :
    hammingDist (fun q => received (Fin.cast same q)) (fun q => target (Fin.cast same q)) =
      hammingDist received target := by
  subst N
  rfl

/-- Actual authenticated records covering a common agreement set inside the Gao
radius recover every live lane. No fixed-target proximity is assumed. -/
theorem decodeRecords_of_heavy (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (redundancy : width input.config < blockLength input.config)
    (authenticated : ∀ record ∈ records, record.2 = input.root[record.1.val]!)
    (H : Finset (Fin (blockLength input.config)))
    (covered : ∀ q ∈ H, ∃ record ∈ records, record.1 = q)
    (enough : 2 * (blockLength input.config - H.card) ≤ blockLength input.config - width input.config)
    (w : Witness input.config input.lanes)
    (agrees : ∀ q ∈ H, ∀ lane : Fin input.lanes,
      E.ofK (recordLane input.lanes input.root[q.val]! lane.val) =
        (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
          ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]!) :
    (decodeRecords input records noWrap).1 = some w := by
  apply decodeRecords_recovers input records noWrap redundancy w
  intro lane
  have distance := receivedLane_distance input records authenticated H covered w agrees lane
  have size : (ConcreteRowExtraction.domain
      (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) noWrap).n =
      blockLength input.config := ConcreteRowExtraction.domain_size _ _
  have receivedEqual : (Vector.mk (Array.ofFn (receivedLane input records lane)) (by simp) :
      Vector E (ConcreteRowExtraction.domain
        (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) noWrap).n).get =
      fun q => receivedLane input records lane (Fin.cast size q) := by
    funext q
    simp [Vector.get, Fin.cast]
  rw [receivedEqual]
  change 2 * hammingDist (fun q => receivedLane input records lane (Fin.cast size q))
    (fun q => (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
      ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[(Fin.cast size q).val]!) ≤ _
  rw [hammingDist_index_cast size (receivedLane input records lane)
    (fun q => (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
      ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]!)]
  exact (Nat.mul_le_mul_left 2 distance).trans enough

/-- Coverage supplies the deduplicated common-coordinate certificate used by
finish, not merely independent per-lane agreement sets. -/
theorem commonCoordinates_of_heavy (input : Public) (records : List (Record input.config))
    (authenticated : ∀ record ∈ records, record.2 = input.root[record.1.val]!)
    (H : Finset (Fin (blockLength input.config)))
    (covered : ∀ q ∈ H, ∃ record ∈ records, record.1 = q)
    (candidate : Array E)
    (matching : ∀ q ∈ H, rowMatches input.config input.lanes
      (encodedLanes input.config candidate) (q, input.root[q.val]!) = true) :
    H ⊆ commonCoordinates input.config input.lanes candidate records := by
  intro q member
  obtain ⟨record, recorded, coordinate⟩ := covered q member
  have value := authenticated record recorded
  have matched : rowMatches input.config input.lanes (encodedLanes input.config candidate) record = true := by
    rcases record with ⟨position, row⟩
    dsimp only at coordinate value
    subst position
    simpa only [value] using matching q member
  exact List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨record, List.mem_filter.mpr ⟨recorded, matched⟩, coordinate⟩)

/-- Every original claim is checked after recovering the same witness. -/
theorem decodeAndCheck_of_heavy (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (laneBound : input.lanes ≤ laneCount input.config)
    (redundancy : width input.config < blockLength input.config)
    (authenticated : ∀ record ∈ records, record.2 = input.root[record.1.val]!)
    (H : Finset (Fin (blockLength input.config)))
    (covered : ∀ q ∈ H, ∃ record ∈ records, record.1 = q)
    (radiusSize : 2 * (blockLength input.config - H.card) ≤ blockLength input.config - width input.config)
    (certificateSize : ParameterBounds.threshold input.config 0 ≤ H.card)
    (w : Witness input.config input.lanes)
    (agrees : ∀ q ∈ H, ∀ lane : Fin input.lanes,
      E.ofK (recordLane input.lanes input.root[q.val]! lane.val) =
        (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
          ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[q.val]!)
    (matching : ∀ q ∈ H, rowMatches input.config input.lanes
      (encodedLanes input.config (paddedWitness input.config input.lanes w))
      (q, input.root[q.val]!) = true)
    (claims : ∀ claim ∈ input.claims.toList,
      dot (paddedWitness input.config input.lanes w) claim.weight = claim.value) :
    (decodeAndCheck input records noWrap).1 = some w := by
  have recovered := decodeRecords_of_heavy input records noWrap redundancy
    authenticated H covered radiusSize w agrees
  have support := (Finset.card_le_card
    (commonCoordinates_of_heavy input records authenticated H covered _ matching))
  have size : (paddedWitness input.config input.lanes w).size =
      laneCount input.config * width input.config := by
    simp only [paddedWitness, tab, Array.size_map, List.size_toArray, List.length_range]
    rw [← Nat.pow_add, Nat.add_sub_of_le foldBound]
  have checked : verified input (paddedWitness input.config input.lanes w) records = true := by
    simp only [verified, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨size, certificateSize.trans support⟩, ?_⟩
    rw [← Array.all_toList]
    exact List.all_eq_true.mpr (fun claim member => beq_iff_eq.mpr (claims claim member))
  have projected : InitialCandidates.project input.config input.lanes
      (paddedWitness input.config input.lanes w) = w := by
    funext i
    have limit : i.val < 2 ^ input.config.logN := by
      have occupied := Nat.mul_le_mul_right (width input.config) laneBound
      rw [← size] at occupied
      simp only [paddedWitness, tab, Array.size_map, List.size_toArray, List.length_range] at occupied
      exact i.isLt.trans_le occupied
    simp [InitialCandidates.project, paddedWitness, tab, getElem!_pos, limit, i.isLt, E.ofK]
  simp only [decodeAndCheck, recovered, Option.bind_some, finish, ite_eq_left checked, projected]

/-- Zero-filled missing observations cannot substitute for a certificate.
In particular a withholding/rejected collector with no records cannot finish. -/
theorem decodeAndCheck_empty (input : Public)
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (thresholdPositive : 0 < ParameterBounds.threshold input.config 0) :
    (decodeAndCheck input [] noWrap).1 = none := by
  simp only [decodeAndCheck]
  cases result : (decodeRecords input [] noWrap).1 with
  | none => rfl
  | some w =>
    simp [finish, verified, commonCoordinates, not_le.mpr thresholdPositive]

#print axioms decodeRecords_of_heavy
#print axioms commonCoordinates_of_heavy
end Whir.SupportedCandidateRecovery
