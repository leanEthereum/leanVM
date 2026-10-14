import Whir.InitialCandidates
import Whir.InitialBatching
import Whir.VerifierInvariant

/-! The commitment-only base-field list and the actual public-claim batching
establish the incoming lost invariant without selecting a list after challenges. -/
namespace Whir.InitialSoundness
open Concrete Protocol CausalGame InitialCandidates

/-- Every extension candidate has exactly the verifier's padded input width. -/
theorem candidate_size (p : ParameterBounds.Profile) (lanes : Nat) (root : BaseOracle)
    (lane_bound : lanes ≤ 2 ^ (ParameterBounds.config p).folds[0]!)
    (a : Array E) (ha : a ∈ extensionCandidates (ParameterBounds.config p) lanes root) :
    a.size = 2 ^ (ParameterBounds.config p).logN := by
  rw [production_reconstruction p lanes root lane_bound a ha]
  simp [paddedWitness, tab]

/-- Quantifiers over the commitment-fixed literal K witnesses imply the exact
finite indexed claim predicate used by the actual batching proof. -/
theorem initial_lost (p : ParameterBounds.Profile) (lanes : Nat) (root : BaseOracle)
    (lane_bound : lanes ≤ 2 ^ (ParameterBounds.config p).folds[0]!) (claims : Array Claim)
    (hfalse : ¬ ∃ w ∈ witnesses (ParameterBounds.config p) lanes root,
      ∀ claim ∈ claims.toList,
        dot (paddedWitness (ParameterBounds.config p) lanes w) claim.weight = claim.value) :
    InitialBatching.Lost (extensionCandidates (ParameterBounds.config p) lanes root) claims := by
  intro a ha
  obtain ⟨claim, hc, hneq⟩ := production_candidate_violates_claim p lanes root
    lane_bound claims hfalse a ha
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc
  let index : Fin claims.size := ⟨j.val, by simp⟩
  have selected : claims[index] = claim := by simpa [index, List.get_eq_getElem] using hj
  exact ⟨index, by simpa only [selected] using hneq⟩

/-- This is the actual initialized verifier's state. The adversarial intro can
be chosen after lambda and is deliberately unrestricted. -/
theorem batching_preserves_lost (p : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (lane_bound : lanes ≤ 2 ^ (ParameterBounds.config p).folds[0]!)
    (claims : Array Claim)
    (hfalse : ¬ ∃ w ∈ witnesses (ParameterBounds.config p) lanes root,
      ∀ claim ∈ claims.toList,
        dot (paddedWitness (ParameterBounds.config p) lanes w) claim.weight = claim.value)
    (lambda : E) (intro : Message E)
    (outside : lambda ∉ InitialBatching.candidateEscape
      (extensionCandidates (ParameterBounds.config p) lanes root) claims) :
    VerifierInvariant.Lost (extensionCandidates (ParameterBounds.config p) lanes root)
      ⟨(batchClaims (2 ^ (ParameterBounds.config p).logN) claims lambda).weight,
       (batchClaims (2 ^ (ParameterBounds.config p).logN) claims lambda).value, intro⟩ :=
  InitialBatching.lost_preserved _ _ claims lambda (candidate_size p lanes root lane_bound)
    (initial_lost p lanes root lane_bound claims hfalse) outside

/-- Exact production list cap and exact 192-bit field cardinality bound the
initial event, retaining the public claim count instead of postulating a cap. -/
theorem initial_escape_probability (p : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (lane_bound : lanes ≤ 2 ^ (ParameterBounds.config p).folds[0]!)
    (claims : Array Claim)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (ParameterBounds.config p).logN) :
    Soundness.uniformProb (InitialBatching.candidateEscape
      (extensionCandidates (ParameterBounds.config p) lanes root) claims) ≤
      ((claims.size - 1 : Nat) : ℚ) / 2 ^ 160 := by
  have bounded := InitialBatching.candidate_escape_probability
    (extensionCandidates (ParameterBounds.config p) lanes root) claims
    (fun a ha j => (shape j).trans (candidate_size p lanes root lane_bound a ha).symm)
  have card : ((extensionCandidates (ParameterBounds.config p) lanes root).card : ℚ) ≤ 2 ^ 32 := by
    exact_mod_cast production_extension_card p lanes root
  calc
    _ ≤ ((extensionCandidates (ParameterBounds.config p) lanes root).card : ℚ) *
        (claims.size - 1 : Nat) / 2 ^ 192 := bounded
    _ ≤ (2 ^ 32 : ℚ) * (claims.size - 1 : Nat) / 2 ^ 192 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right card (by positivity)) (by positivity)
    _ = _ := by ring

end Whir.InitialSoundness
