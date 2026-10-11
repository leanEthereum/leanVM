import Whir.BaseCandidateDescent
import Whir.ConcreteCandidates

/-! The initial list is fixed by the pruned base commitment. Its live leaf lanes
are reversed to coefficient order; missing lanes are zero. Checked base-field
interpolation forces every extension candidate to reconstruct a literal witness.

`witnesses` is the deterministic live-c0 image of `extensionCandidates`, before
either claims or an opening strategy is supplied. Supported production profiles
give the actual novel-encoder list cap `2^32` and sufficient matching points for
base descent. `production_candidate_violates_claim` transfers a false statement
about this fixed K list to every E candidate for initial batching.

The total oracle also assigns a list to malformed roots; no root-shape premise
is needed for interpolation. `fullRow_reverse` identifies valid occupied leaves
with the verifier's reversal. Rejection of malformed roots remains the actual
verifier's separate shape check. -/
namespace Whir.InitialCandidates
open Concrete CandidateFolding Protocol

/-- Complete ascending row oracle, before any opening or challenge is chosen. -/
def fullRow (c : Config) (lanes : ℕ) (root : CausalGame.BaseOracle) :
    Fin (2^c.folds[0]!) → Fin (2^(c.logN-c.folds[0]!+c.rates[0]!)) → K :=
  fun lane q => if lane.val < lanes then (root[q.val]!)[lanes-1-lane.val]! else 0

/-- A well-shaped occupied leaf is reversed exactly as in the verifier's base
query reduction, with zero entries for the pruned lanes. -/
theorem fullRow_reverse (c : Config) (lanes : ℕ) (root : CausalGame.BaseOracle)
    (q : Fin (2^(c.logN-c.folds[0]!+c.rates[0]!)))
    (shape : root[q.val]!.size = lanes) (lane : Fin (2^c.folds[0]!)) :
    fullRow c lanes root lane q =
      if lane.val < lanes then (root[q.val]!.reverse)[lane.val]! else 0 := by
  by_cases h : lane.val < lanes
  · have hr : lane.val < root[q.val]!.size := by omega
    have hs : lanes-1-lane.val < root[q.val]!.size := by omega
    simp only [fullRow, h, ↓reduceIte,
      getElem!_pos (root[q.val]!) (lanes-1-lane.val) hs,
      getElem!_pos (root[q.val]!.reverse) lane.val (by simpa using hr),
      Array.getElem_reverse, shape]
  · simp [fullRow, h]

/-- The initial extension list uses the actual dense novel-basis encoder. -/
noncomputable def extensionCandidates (c : Config) (lanes : ℕ)
    (root : CausalGame.BaseOracle) : Finset (Array E) :=
  arrayCandidates true (concreteEncoder (c.logN-c.folds[0]!) c.rates[0]!)
    (fun lane q => E.ofK (fullRow c lanes root lane q)) (ParameterBounds.threshold c 0)

/-- Deterministic projection of live coefficients; no decoding choice is made. -/
def project (c : Config) (lanes : ℕ) (a : Array E) : CausalGame.Witness c lanes :=
  fun i => a[i.val]!.c0

/-- Commitment-only candidate list, independent of public claims and strategy. -/
noncomputable def witnesses (c : Config) (lanes : ℕ) (root : CausalGame.BaseOracle) :
    Finset (CausalGame.Witness c lanes) := by
  classical
  exact (extensionCandidates c lanes root).image (project c lanes)

theorem witnesses_card_le (c : Config) (lanes : ℕ) (root : CausalGame.BaseOracle) :
    (witnesses c lanes root).card ≤ (extensionCandidates c lanes root).card := by
  classical
  exact Finset.card_image_le

private noncomputable def baseRepresentation : AdditiveCode.BaseRepresentation FieldModel.BaseQuotient where
  map := FieldModel.toBaseQuotient
  one := FieldModel.toBaseQuotient_one
  add := FieldModel.toBaseQuotient_xor
  mul := FieldModel.toBaseQuotient_kmul
  inv := FieldModel.toBaseQuotient_kinv

/-- The actual machine basis and domain meet the interpolation prerequisites. -/
theorem coefficient_restriction (c : Config) (lanes : ℕ) (root : CausalGame.BaseOracle)
    (depth : c.logN-c.folds[0]!+c.rates[0]! ≤ 64)
    (threshold : 2^(c.logN-c.folds[0]!)-1 < ParameterBounds.threshold c 0)
    (a : Array E) (ha : a ∈ extensionCandidates c lanes root) :
    ∃ words : Fin (2^c.folds[0]!) → Fin (2^(c.logN-c.folds[0]!)) → K,
      (∀ l j, E.ofK (words l j) = unpack true (2^c.folds[0]!)
        (2^(c.logN-c.folds[0]!)) a l j) ∧
      (∀ l, lanes ≤ l.val → ∀ j, words l j = 0) := by
  classical
  obtain ⟨_, s, hs, hmatch⟩ := (arrayCandidates_mem_iff _ _ _ _ _).mp ha
  simp only [← Nat.not_lt]
  apply BaseCandidateDescent.actual_word_candidates_restrict
    (fun j => (1 : K) <<< UInt64.ofNat j) (c.logN-c.folds[0]!)
    (AdditiveCode.bitBasis_independent baseRepresentation
      FieldModel.toBaseQuotient_injective _ (by omega))
    s (fun q => UInt64.ofNat q.val) ?_
    (fullRow c lanes root) {l | l.val < lanes} ?_ _
    (ParameterBounds.threshold c 0) threshold hs hmatch
  · intro i hi j hj heq
    apply Fin.ext
    apply AdditiveCode.evaluationPoint_injective AdditiveCode.concreteBaseRepresentation
      FieldModel.ofK_injective
      (i.isLt.trans_le (Nat.pow_le_pow_right (by decide) depth))
      (j.isLt.trans_le (Nat.pow_le_pow_right (by decide) depth))
    exact congrArg E.ofK heq
  · intro l hl i hi
    change ¬ l.val < lanes at hl
    simp [fullRow, hl]

/-- Every initial extension candidate is exactly the zero-padded literal live
base witness obtained by its c0 projection. There is no descent assumption. -/
theorem reconstruction (c : Config) (lanes : ℕ) (root : CausalGame.BaseOracle)
    (fold_bound : c.folds[0]! ≤ c.logN)
    (_lane_bound : lanes ≤ 2^c.folds[0]!)
    (depth : c.logN-c.folds[0]!+c.rates[0]! ≤ 64)
    (threshold : 2^(c.logN-c.folds[0]!)-1 < ParameterBounds.threshold c 0)
    (a : Array E) (ha : a ∈ extensionCandidates c lanes root) :
    a = CausalGame.paddedWitness c lanes (project c lanes a) := by
  obtain ⟨words, hwords, hzero⟩ := coefficient_restriction c lanes root depth threshold a ha
  have hsize := arrayCandidates_size true
    (concreteEncoder (c.logN-c.folds[0]!) c.rates[0]!)
    (fun lane q => E.ofK (fullRow c lanes root lane q)) (ParameterBounds.threshold c 0) a ha
  have hwidth : 2^c.folds[0]! * 2^(c.logN-c.folds[0]!) = 2^c.logN := by
    rw [← Nat.pow_add, Nat.add_sub_of_le fold_bound]
  have hpos : 0 < 2^(c.logN-c.folds[0]!) := Nat.pow_pos (by decide)
  apply Array.ext
  · simpa [CausalGame.paddedWitness, tab, hwidth] using hsize
  · intro i hi hi'
    let l : Fin (2^c.folds[0]!) := ⟨i / 2^(c.logN-c.folds[0]!),
      (Nat.div_lt_iff_lt_mul hpos).mpr (by simpa [hsize, Nat.mul_comm] using hi)⟩
    let j : Fin (2^(c.logN-c.folds[0]!)) := ⟨i % 2^(c.logN-c.folds[0]!), Nat.mod_lt _ hpos⟩
    have hind : j.val + 2^(c.logN-c.folds[0]!) * l.val = i := by
      exact Nat.mod_add_div i (2^(c.logN-c.folds[0]!))
    have hw : E.ofK (words l j) = a[i]! := by
      simpa [unpack, topIndex, hind] using hwords l j
    have hw' : E.ofK (words l j) = a[i] := by simpa only [getElem!_pos a i hi] using hw
    by_cases hlive : i < lanes * 2^(c.logN-c.folds[0]!)
    · simp [CausalGame.paddedWitness, tab, hlive, project,
        getElem!_pos a i hi, ← hw', E.ofK]
    · have hl : lanes ≤ l.val := by
        dsimp [l]
        exact (Nat.le_div_iff_mul_le hpos).mpr (by omega)
      have hz : a[i]! = E.ofK 0 := by rw [← hw, hzero l hl j]
      simpa [CausalGame.paddedWitness, tab, hlive, getElem!_pos a i hi] using hz

/-- A false public multi-claim statement leaves no original E candidate satisfying
all claims, the exact premise needed for the first powers batch. -/
theorem candidate_violates_claim (c : Config) (lanes : ℕ) (root : CausalGame.BaseOracle)
    (fold_bound : c.folds[0]! ≤ c.logN) (lane_bound : lanes ≤ 2^c.folds[0]!)
    (depth : c.logN-c.folds[0]!+c.rates[0]! ≤ 64)
    (threshold : 2^(c.logN-c.folds[0]!)-1 < ParameterBounds.threshold c 0)
    (claims : Array CausalGame.Claim)
    (hfalse : ¬ ∃ w ∈ witnesses c lanes root, ∀ claim ∈ claims.toList,
      dot (CausalGame.paddedWitness c lanes w) claim.weight = claim.value)
    (a : Array E) (ha : a ∈ extensionCandidates c lanes root) :
    ∃ claim ∈ claims.toList, dot a claim.weight ≠ claim.value := by
  classical
  by_contra h
  push Not at h
  apply hfalse
  refine ⟨project c lanes a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
  intro claim hc
  rw [← reconstruction c lanes root fold_bound lane_bound depth threshold a ha]
  exact h claim hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Initial indexing and interpolation arithmetic for the supported production
profiles, checked on the actual configuration generator. -/
theorem production_initial_facts : ∀ p : ParameterBounds.Profile,
    let c := ParameterBounds.config p
    CausalGame.remaining c 0 = c.logN-c.folds[0]! ∧
    c.folds[0]! ≤ c.logN ∧
    c.logN-c.folds[0]!+c.rates[0]! ≤ 64 ∧
    2^(c.logN-c.folds[0]!)-1 < ParameterBounds.threshold c 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem production_extension_card (p : ParameterBounds.Profile) (lanes : ℕ)
    (root : CausalGame.BaseOracle) :
    (extensionCandidates (ParameterBounds.config p) lanes root).card ≤ 2^32 := by
  have h := ConcreteCandidates.production_arrayCandidates_card true p
    ⟨0, (ParameterBounds.production_config_valid p).2.1⟩
    (lanes := 2^(ParameterBounds.config p).folds[0]!)
  unfold ParameterBounds.length at h
  dsimp only at h
  rw [(production_initial_facts p).1] at h
  exact h (fun lane q => E.ofK (fullRow (ParameterBounds.config p) lanes root lane q))

theorem production_witnesses_card (p : ParameterBounds.Profile) (lanes : ℕ)
    (root : CausalGame.BaseOracle) :
    (witnesses (ParameterBounds.config p) lanes root).card ≤ 2^32 :=
  (witnesses_card_le _ _ _).trans (production_extension_card p lanes root)

theorem production_reconstruction (p : ParameterBounds.Profile) (lanes : ℕ)
    (root : CausalGame.BaseOracle)
    (lane_bound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (a : Array E) (ha : a ∈ extensionCandidates (ParameterBounds.config p) lanes root) :
    a = CausalGame.paddedWitness (ParameterBounds.config p) lanes
      (project (ParameterBounds.config p) lanes a) :=
  reconstruction _ lanes root (production_initial_facts p).2.1 lane_bound
    (production_initial_facts p).2.2.1 (production_initial_facts p).2.2.2 a ha

theorem production_candidate_violates_claim (p : ParameterBounds.Profile) (lanes : ℕ)
    (root : CausalGame.BaseOracle)
    (lane_bound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (claims : Array CausalGame.Claim)
    (hfalse : ¬ ∃ w ∈ witnesses (ParameterBounds.config p) lanes root,
      ∀ claim ∈ claims.toList, dot (CausalGame.paddedWitness (ParameterBounds.config p)
        lanes w) claim.weight = claim.value)
    (a : Array E) (ha : a ∈ extensionCandidates (ParameterBounds.config p) lanes root) :
    ∃ claim ∈ claims.toList, dot a claim.weight ≠ claim.value :=
  candidate_violates_claim _ lanes root (production_initial_facts p).2.1 lane_bound
    (production_initial_facts p).2.2.1 (production_initial_facts p).2.2.2 claims hfalse a ha

end Whir.InitialCandidates
