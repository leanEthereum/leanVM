import Whir.CountedCandidateCheckArithmetic

/-! Value-connected instrumentation of the cached common-coordinate checker. Every original public claim is evaluated. No commitment is recomputed and no intermediate GS decoder is invoked. The input contract is independent of acceptance and explicitly bounds claims, records, dimensions and physical rows. -/
namespace Whir.CountedCandidateCheck
open Concrete Protocol CausalGame SupportedCandidateExtraction CandidateFolding
open scoped BigOperators

/-- Run one actual dense source encoding per padded lane and retain both outputs. -/
def countedEncodedLanes (c : Config) (candidate : Array E) : Array (Array E) × Nat :=
  let encoded := Array.ofFn fun lane : Fin (laneCount c) =>
    countedEncode (c.logN - c.folds[0]!) c.rates[0]!
      (Array.ofFn (unpack true (laneCount c) (width c) candidate lane))
  (encoded.map Prod.fst, (encoded.map Prod.snd).toList.sum)

theorem countedEncodedLanes_value (c : Config) (candidate : Array E) :
    (countedEncodedLanes c candidate).1 = encodedLanes c candidate := by
  simp [countedEncodedLanes, encodedLanes, Array.map_ofFn, Function.comp_def, countedEncode_value]

def encoderBound (c : Config) : Nat :=
  laneCount c * blockLength c *
    (2 * (c.logN - c.folds[0]!) * (c.logN - c.folds[0]!) +
      131 * (c.logN - c.folds[0]!) + 5 * width c)

theorem countedEncodedLanes_cost (c : Config) (candidate : Array E) :
    (countedEncodedLanes c candidate).2 ≤ encoderBound c := by
  simp only [countedEncodedLanes, Array.toList_map, Array.toList_ofFn,
    List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _lane : Fin (laneCount c), blockLength c *
        (2 * (c.logN - c.folds[0]!) * (c.logN - c.folds[0]!) +
          131 * (c.logN - c.folds[0]!) + 5 * width c) := by
      apply Finset.sum_le_sum
      intro lane _
      exact countedEncode_cost _ _ _
    _ = encoderBound c := by simp [encoderBound, Nat.mul_assoc]

/-- Full all-claim check: the pair array shares each actual dot result with its counter. Eager checking bounds the source short-circuit implementation too. -/
def countedClaims (input : Public) (candidate : Array E) : Bool × Nat :=
  let checked := input.claims.map fun claim =>
    let result := countedDot candidate claim.weight
    (result.1 == claim.value, result.2)
  ((checked.map Prod.fst).all id, (checked.map Prod.snd).toList.sum)

theorem countedClaims_value (input : Public) (candidate : Array E) :
    (countedClaims input candidate).1 =
      input.claims.all (fun claim => dot candidate claim.weight == claim.value) := by
  simp [countedClaims, countedDot, Array.map_map, Function.comp_def]

theorem countedClaims_cost (input : Public) (candidate : Array E) :
    (countedClaims input candidate).2 ≤ input.claims.size * (2 * candidate.size) := by
  simp only [countedClaims, Array.map_map, Array.toList_map, Function.comp_def, countedDot]
  have h := List.sum_le_length_nsmul
    (input.claims.toList.map fun claim => 2 * min candidate.size claim.weight.size)
    (2 * candidate.size) (by
      intro cost member
      obtain ⟨claim, _, rfl⟩ := List.mem_map.mp member
      exact Nat.mul_le_mul_left 2 (Nat.min_le_left _ _))
  simpa [Nat.mul_comm] using h

/-- The expensive cache is outside the record loop. Comparisons and coordinate set construction contribute no field operations. -/
def countedVerified (input : Public) (candidate : Array E)
    (records : List (Record input.config)) : Bool × Nat :=
  if candidate.size == laneCount input.config * width input.config then
    let encoded := countedEncodedLanes input.config candidate
    let common := ((records.filter (rowMatches input.config input.lanes encoded.1)).map Prod.fst).toFinset
    let claims := countedClaims input candidate
    (decide (ParameterBounds.threshold input.config 0 ≤ common.card) && claims.1,
      encoded.2 + claims.2)
  else (false, 0)

theorem countedVerified_value (input : Public) (candidate : Array E)
    (records : List (Record input.config)) :
    (countedVerified input candidate records).1 = verified input candidate records := by
  unfold countedVerified verified commonCoordinates
  split <;> simp_all [countedEncodedLanes_value, countedClaims_value]

def checkerBound (input : Public) : Nat :=
  encoderBound input.config + input.claims.size * (2 * laneCount input.config * width input.config)

theorem countedVerified_cost (input : Public) (candidate : Array E)
    (records : List (Record input.config)) :
    (countedVerified input candidate records).2 ≤ checkerBound input := by
  unfold countedVerified
  split
  · rename_i shape
    have shape : candidate.size = laneCount input.config * width input.config := by
      exact beq_iff_eq.mp shape
    have he := countedEncodedLanes_cost input.config candidate
    have hc := countedClaims_cost input candidate
    dsimp only
    rw [shape] at hc
    unfold checkerBound
    nlinarith
  · exact Nat.zero_le _

def countedFinish (input : Public) (candidate : Array E)
    (records : List (Record input.config)) : Option (Witness input.config input.lanes) × Nat :=
  let checked := countedVerified input candidate records
  (if checked.1 then some (InitialCandidates.project input.config input.lanes candidate) else none,
    checked.2)

theorem countedFinish_value (input : Public) (candidate : Array E)
    (records : List (Record input.config)) :
    (countedFinish input candidate records).1 = finish input candidate records := by
  simp [countedFinish, finish, countedVerified_value]

theorem countedFinish_cost (input : Public) (candidate : Array E)
    (records : List (Record input.config)) :
    (countedFinish input candidate records).2 ≤ checkerBound input :=
  countedVerified_cost input candidate records

/-- Strict resource contract. Raw prover replies are external oracle output; bounded consumed records and public input are a separate explicit premise. -/
structure ConsumerInput (input : Public) (recordLimit claimLimit : Nat)
    (records : List (Record input.config)) : Prop where
  foldBound : input.config.folds[0]! ≤ input.config.logN
  noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64
  lanes : input.lanes ≤ laneCount input.config
  recordCount : records.length ≤ recordLimit
  recordRows : ∀ record ∈ records, record.2.size = input.lanes
  claims : input.claims.size ≤ claimLimit
  claimWeights : ∀ claim ∈ input.claims.toList, claim.weight.size = laneCount input.config * width input.config
  rootRows : input.root.size = blockLength input.config
  rootLanes : ∀ row ∈ input.root.toList, row.size = input.lanes

/-- Single-variable field-arithmetic polynomial after the transparent no-wrap restriction. The degree-seven Gao term is added by the complete extractor. -/
def checkerPolynomial (lanes nodes claims : Nat) : Nat :=
  lanes * nodes * (16576 + 5 * nodes) + claims * (2 * lanes * nodes)

theorem checkerBound_polynomial (input : Public)
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    checkerBound input ≤ checkerPolynomial (laneCount input.config)
      (blockLength input.config) input.claims.size := by
  have depth : input.config.logN - input.config.folds[0]! ≤ 64 := by omega
  have widthBound : width input.config ≤ blockLength input.config := by
    apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    omega
  have square : 2 * (input.config.logN - input.config.folds[0]!) *
      (input.config.logN - input.config.folds[0]!) +
      131 * (input.config.logN - input.config.folds[0]!) ≤ 16576 := by nlinarith
  unfold checkerBound encoderBound checkerPolynomial
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left _ (by omega)
  · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ widthBound)

end Whir.CountedCandidateCheck
