import Whir.PCSListExtraction
import Whir.SupportedCandidateFolding

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-! Intermediate extension rows are LIST decoded with dense GS interpolation,
Roth--Ruckenstein and the actual Shoup root backend. The Cartesian assembly is
computable and never enumerates the extension field. Integer parameters are
checked before invoking the backend. -/
namespace Whir.InterleavedListExtraction
open Concrete CompPoly
local instance : Field E := ExtractionField.field

/-- Run the real backend only after its decidable integer certificate passes. -/
def lanePolynomials (n rate errors multiplicity weightedDegree : Nat)
    (received : Fin (2 ^ (n + rate)) → E) : List (CPolynomial E) :=
  let params := _root_.GuruswamiSudan.execParamsOfMultiplicityAndDegree
    (2 ^ n) errors multiplicity weightedDegree
  if _root_.GuruswamiSudan.paramsPassIntegerChecks (2 ^ n) (2 ^ (n + rate)) errors params then
    (PCSListExtraction.listPolynomials (n + rate) params received).toList
  else []

/-- Deduplication is by literal recovered E coefficient arrays. -/
def laneWords (n rate errors multiplicity weightedDegree : Nat)
    (received : Fin (2 ^ (n + rate)) → E) : List (Array E) :=
  ((lanePolynomials n rate errors multiplicity weightedDegree received).map
    (ConcreteRowExtraction.coefficients n)).dedup

def cartesian {α : Type*} : List (List α) → List (List α)
  | [] => [[]]
  | first :: rest => first.flatMap (fun value => (cartesian rest).map (value :: ·))

@[simp] theorem mem_cartesian {α : Type*} (choices : List (List α)) (values : List α) :
    values ∈ cartesian choices ↔ List.Forall₂ (fun value options => value ∈ options) values choices := by
  induction choices generalizing values with
  | nil => cases values <;> simp [cartesian]
  | cons first rest ih =>
    cases values with
    | nil => simp [cartesian]
    | cons value tail => simp [cartesian, ih, List.forall₂_cons]

/-- Packing applies the inverse novel-basis transform to every E lane. It never
silently c0-projects intermediate extension coefficients. -/
def assemble (n : Nat) (top : Bool) (rows : List (Array E)) : Array E :=
  if top then rows.toArray.flatten
  else
    let cached := rows.toArray
    Array.ofFn fun i : Fin (rows.length * 2 ^ n) =>
      (cached[i.val % rows.length]!)[i.val / rows.length]!

def candidates (n rate lanes errors multiplicity weightedDegree : Nat) (top : Bool)
    (received : Fin lanes → Fin (2 ^ (n + rate)) → E) : List (Array E) :=
  (cartesian (List.ofFn fun lane =>
    laneWords n rate errors multiplicity weightedDegree (received lane))).map (assemble n top)

theorem lanePolynomials_complete (n rate errors multiplicity weightedDegree : Nat)
    (noWrap : n + rate ≤ 64)
    (checked : _root_.GuruswamiSudan.paramsPassIntegerChecks (2 ^ n) (2 ^ (n + rate)) errors
      (_root_.GuruswamiSudan.execParamsOfMultiplicityAndDegree
        (2 ^ n) errors multiplicity weightedDegree) = true)
    (received : Fin (2 ^ (n + rate)) → E) (polynomial : Polynomial E)
    (degree : polynomial.degree < (2 ^ n : Nat))
    (distance : hammingDist received (fun i => polynomial.eval (E.ofK (UInt64.ofNat i.val))) ≤ errors) :
    ∃ candidate ∈ lanePolynomials n rate errors multiplicity weightedDegree received,
      candidate.toPoly = polynomial := by
  have certificate := (_root_.GuruswamiSudan.paramsPassIntegerChecks_iff _ _ _ _).mp checked
  simpa only [lanePolynomials, checked, ↓reduceIte] using
    PCSListExtraction.listPolynomials_complete n rate noWrap _ errors certificate received polynomial degree distance

theorem polynomial_coefficients (n : Nat) (noWrap : n ≤ 64) (p : CPolynomial E)
    (degree : p.toPoly.degree < (2 ^ n : Nat)) :
    (ConcreteRowExtraction.coefficients n p).size = 2 ^ n ∧
      AdditiveCode.concretePolynomial n (ConcreteRowExtraction.coefficients n p) = p.toPoly := by
  obtain ⟨a, ha⟩ := (@AdditiveCode.polynomial_surjective E FieldModel.instFieldE
    (AdditiveCode.bitBasis E.ofK) inferInstance n
    (AdditiveCode.concrete_bitBasis_independent n noWrap) p.toPoly).mpr degree
  have polynomial : AdditiveCode.concretePolynomial n (Array.ofFn a) = p.toPoly := by
    simpa [AdditiveCode.concretePolynomial, AdditiveCode.arrayPolynomial,
      AdditiveCode.concreteBaseRepresentation, QueryRefinement.concreteRepresentation] using ha
  have recover := ConcreteRowExtraction.coefficients_recovers n noWrap
    (Array.ofFn a) (by simp) p polynomial.symm
  rw [recover]
  exact ⟨by simp, polynomial⟩

theorem laneWords_complete (n rate errors multiplicity weightedDegree : Nat)
    (noWrap : n + rate ≤ 64)
    (checked : _root_.GuruswamiSudan.paramsPassIntegerChecks (2 ^ n) (2 ^ (n + rate)) errors
      (_root_.GuruswamiSudan.execParamsOfMultiplicityAndDegree
        (2 ^ n) errors multiplicity weightedDegree) = true)
    (received : Fin (2 ^ (n + rate)) → E) (words : Array E) (shape : words.size = 2 ^ n)
    (distance : hammingDist received
      (fun i => (encode n rate words)[i.val]!) ≤ errors) :
    words ∈ laneWords n rate errors multiplicity weightedDegree received := by
  obtain ⟨p, member, polynomial⟩ := lanePolynomials_complete n rate errors multiplicity weightedDegree
    noWrap checked received (AdditiveCode.concretePolynomial n words)
    (AdditiveCode.concrete_polynomial_degree_lt n (by omega) words) (by
      convert distance using 1
      congr 1
      funext i
      exact (AdditiveCode.concrete_encode_eval n rate words shape i.val i.isLt).symm)
  have recover := ConcreteRowExtraction.coefficients_recovers n (by omega) words shape p polynomial
  simp only [laneWords, List.mem_dedup, List.mem_map]
  exact ⟨p, member, recover⟩

/-- Whole interleaved candidate completeness, with each target lane decoded by
the actual GS backend before deterministic Cartesian packing. -/
theorem candidates_complete (n rate lanes errors multiplicity weightedDegree : Nat)
    (top : Bool) (noWrap : n + rate ≤ 64)
    (checked : _root_.GuruswamiSudan.paramsPassIntegerChecks (2 ^ n) (2 ^ (n + rate)) errors
      (_root_.GuruswamiSudan.execParamsOfMultiplicityAndDegree
        (2 ^ n) errors multiplicity weightedDegree) = true)
    (received : Fin lanes → Fin (2 ^ (n + rate)) → E) (words : Fin lanes → Array E)
    (shape : ∀ lane, (words lane).size = 2 ^ n)
    (distance : ∀ lane, hammingDist (received lane)
      (fun i => (encode n rate (words lane))[i.val]!) ≤ errors) :
    assemble n top (List.ofFn words) ∈
      candidates n rate lanes errors multiplicity weightedDegree top received := by
  apply List.mem_map.mpr
  refine ⟨List.ofFn words, (mem_cartesian _ _).mpr ?_, rfl⟩
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp, ?_⟩
  intro i hi hj
  simpa using laneWords_complete n rate errors multiplicity weightedDegree noWrap checked
    (received ⟨i, by simpa using hi⟩) (words ⟨i, by simpa using hi⟩)
    (shape _) (distance _)

open Classical in
theorem laneWords_sound (n rate errors multiplicity weightedDegree threshold : Nat)
    (noWrap : n + rate ≤ 64) (radiusBound : errors + threshold ≤ 2 ^ (n + rate))
    (received : Fin (2 ^ (n + rate)) → E) (words : Array E)
    (member : words ∈ laneWords n rate errors multiplicity weightedDegree received) :
    words ∈ CandidateFolding.arrayCandidates true
      (CandidateFolding.concreteEncoder n rate) (fun _ : Fin 1 => received) threshold := by
  simp only [laneWords, List.mem_dedup, List.mem_map] at member
  obtain ⟨p, hp, rfl⟩ := member
  dsimp only [lanePolynomials] at hp
  split at hp
  · rename_i checked
    have certificate := (_root_.GuruswamiSudan.paramsPassIntegerChecks_iff _ _ _ _).mp checked
    have semantic := (_root_.GuruswamiSudan.mem_decodeWithParams_iff_degree_and_distance
      PCSListExtraction.context _ certificate
      (ωs := AdditiveCode.concreteDomain (n + rate) noWrap)
      (w := PCSListExtraction.receivedWord (n + rate) received) (by rfl)).mp ⟨p, hp, rfl⟩
    obtain ⟨shape, polynomial⟩ := polynomial_coefficients n (by omega) p semantic.1
    apply (CandidateFolding.oneLane_arrayCandidates_mem_iff _ _ _ _ _).mpr
    refine ⟨shape, ?_⟩
    have partition := _root_.GuruswamiSudan.agreement_card_add_hammingDist
      (f := received) (ωs := AdditiveCode.concreteDomain (n + rate) noWrap) p.toPoly
    have count : (Finset.univ.filter (fun i => received i =
        p.toPoly.eval (E.ofK (UInt64.ofNat i.val)))).card ≥ threshold := by
      have distance := semantic.2
      change hammingDist received
        (fun i => p.toPoly.eval (E.ofK (UInt64.ofNat i.val))) ≤ errors at distance
      change (Finset.univ.filter (fun i => received i =
        p.toPoly.eval (E.ofK (UInt64.ofNat i.val)))).card + hammingDist received
        (fun i => p.toPoly.eval (E.ofK (UInt64.ofNat i.val))) = 2 ^ (n + rate) at partition
      omega
    convert count using 1
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ConcreteCandidates.concreteEncoder_ofFn]
    have array : Array.ofFn (fun j : Fin (2 ^ n) =>
        (ConcreteRowExtraction.coefficients n p)[j.val]!) = ConcreteRowExtraction.coefficients n p := by
      apply Array.ext
      · simp [shape]
      · intro i hi hi'
        simp [getElem!_pos, hi']
    rw [array, AdditiveCode.concrete_encode_eval n rate _ shape q.val q.isLt, polynomial]
    exact eq_comm
  · simp at hp

open Classical in
/-- The actual executable per-lane list, after deduplication, inherits the
proved production Johnson cap. No candidate enumeration is used by the algorithm. -/
theorem laneWords_production_bound (profile : ParameterBounds.Profile)
    (level : Fin (ParameterBounds.config profile).folds.size)
    (errors multiplicity weightedDegree : Nat)
    (radiusBound : errors + ParameterBounds.threshold (ParameterBounds.config profile) level ≤
      ParameterBounds.length (ParameterBounds.config profile) level)
    (received : Fin (ParameterBounds.length (ParameterBounds.config profile) level) → E) :
    (laneWords (CausalGame.remaining (ParameterBounds.config profile) level)
      (ParameterBounds.config profile).rates[level.val]! errors multiplicity weightedDegree received).length ≤ 2 ^ 32 := by
  let words := laneWords (CausalGame.remaining (ParameterBounds.config profile) level)
    (ParameterBounds.config profile).rates[level.val]! errors multiplicity weightedDegree received
  have depth : CausalGame.remaining (ParameterBounds.config profile) level +
      (ParameterBounds.config profile).rates[level.val]! ≤ 64 := by
    have bound := (ParameterBounds.production_level_facts profile level).2.2.1
    have small : CausalGame.remaining (ParameterBounds.config profile) level +
        (ParameterBounds.config profile).rates[level.val]! ≤ 26 :=
      (pow_le_pow_iff_right₀ (by decide : (1 : Nat) < 2)).mp bound
    omega
  have subset : words.toFinset ⊆ CandidateFolding.arrayCandidates true
      (CandidateFolding.concreteEncoder (CausalGame.remaining (ParameterBounds.config profile) level)
        (ParameterBounds.config profile).rates[level.val]!)
      (fun _ : Fin 1 => received) (ParameterBounds.threshold (ParameterBounds.config profile) level) := by
    intro word member
    exact laneWords_sound _ _ _ _ _ _ depth radiusBound received word (List.mem_toFinset.mp member)
  have nodup : words.Nodup := List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup nodup]
  exact (Finset.card_le_card subset).trans (ConcreteCandidates.production_arrayCandidates_card true
    profile level (fun _ : Fin 1 => received))

/-- A concrete non-unique-radius E fixture: dimension 4, length 16, eight
agreements. Gao's radius permits six errors, but GS certifies eight. -/
def fixtureParams := _root_.GuruswamiSudan.execParamsOfMultiplicityAndDegree 4 8 2 15

theorem fixture_certificate : _root_.GuruswamiSudan.GSParamCert 4 16 8 fixtureParams :=
  (_root_.GuruswamiSudan.paramsPassIntegerChecks_iff _ _ _ _).mp (by decide)

/-- Exact cardinality of the executable assembly, including duplicates. -/
theorem cartesian_length {α : Type*} (choices : List (List α)) :
    (cartesian choices).length = (choices.map List.length).prod := by
  induction choices with
  | nil => simp [cartesian]
  | cons first rest ih => simp [cartesian, List.length_flatMap, ih]

theorem cartesian_length_le {α : Type*} (choices : List (List α)) (bound : Nat)
    (bounded : ∀ options ∈ choices, options.length ≤ bound) :
    (cartesian choices).length ≤ bound ^ choices.length := by
  rw [cartesian_length]
  simpa only [List.length_map] using List.prod_le_pow_length (choices.map List.length) bound (by
    intro length member
    obtain ⟨options, hoption, rfl⟩ := List.mem_map.mp member
    exact bounded options hoption)

/-- A derived polynomial bound for the actual Cartesian candidate ARRAY output
at supported intermediate levels with at most sixteen lanes. The exponent is
deliberately conservative; this is not a field-size enumeration. It bounds
candidate assembly, not uninstrumented GS-backend running time. -/
theorem candidates_production_polynomial_bound (profile : ParameterBounds.Profile)
    (level : Fin (ParameterBounds.config profile).folds.size)
    (lanes : Nat) (fixedLanes : lanes ≤ 16) (top : Bool)
    (errors multiplicity weightedDegree : Nat)
    (radiusBound : errors + ParameterBounds.threshold (ParameterBounds.config profile) level ≤
      ParameterBounds.length (ParameterBounds.config profile) level)
    (received : Fin lanes → Fin (ParameterBounds.length (ParameterBounds.config profile) level) → E) :
    (candidates (CausalGame.remaining (ParameterBounds.config profile) level)
      (ParameterBounds.config profile).rates[level.val]! lanes errors multiplicity weightedDegree
      top received).length ≤ (ParameterBounds.length (ParameterBounds.config profile) level) ^ 512 := by
  let N := ParameterBounds.length (ParameterBounds.config profile) level
  have size : 2 ≤ N := by
    have facts := ParameterBounds.production_level_facts profile level
    have dimensionPositive := facts.1
    have dimensionBound := facts.2.1
    change _ < N at dimensionBound
    omega
  have count : (candidates (CausalGame.remaining (ParameterBounds.config profile) level)
      (ParameterBounds.config profile).rates[level.val]! lanes errors multiplicity weightedDegree
      top received).length ≤ (2 ^ 32) ^ lanes := by
    unfold candidates
    rw [List.length_map]
    simpa only [List.length_ofFn] using cartesian_length_le
      (List.ofFn fun lane => laneWords (CausalGame.remaining (ParameterBounds.config profile) level)
        (ParameterBounds.config profile).rates[level.val]! errors multiplicity weightedDegree
        (received lane)) (2 ^ 32) (by
          intro options member
          obtain ⟨lane, rfl⟩ := List.mem_ofFn.mp member
          exact laneWords_production_bound profile level errors multiplicity weightedDegree
            radiusBound (received lane))
  calc
    _ ≤ (2 ^ 32) ^ lanes := count
    _ ≤ (N ^ 32) ^ lanes := Nat.pow_le_pow_left (Nat.pow_le_pow_left size 32) lanes
    _ = N ^ (32 * lanes) := (pow_mul N 32 lanes).symm
    _ ≤ N ^ 512 := Nat.pow_le_pow_right (by omega) (by omega)

#print axioms lanePolynomials_complete
#print axioms fixture_certificate
#print axioms mem_cartesian
end Whir.InterleavedListExtraction
