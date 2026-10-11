import Whir.SupportedCandidateFolding

/-! Candidate-specific claim restoration. The existing all-candidates-Lost
causal event is too weak to certify that the SAME lifted witness explains the
original claims; the guarded event below is separately charged. -/
namespace Whir.SupportedCandidateExtraction
open Concrete Protocol CandidateFolding VerifierInvariant

set_option maxRecDepth 100000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [CharP F 2]

noncomputable def candidateRoundEscape (candidates : Finset (Array F))
    (state : VerifierState F) (block : Nat) : Finset F := by
  classical
  exact roundBad (candidates.filter (fun witness => dot witness state.weight ≠ state.claim)) state block

/-- Guarding each false candidate makes its polynomial nonzero without an
all-candidates-Lost premise. -/
theorem candidateRoundEscape_probability (candidates : Finset (Array F))
    (state : VerifierState F) (block : Nat) :
    Soundness.uniformProb (candidateRoundEscape candidates state block) ≤
      (candidates.card : ℚ) * (2 / Fintype.card F) := by
  classical
  have bounded := roundBad_probability
    (candidates.filter (fun witness => dot witness state.weight ≠ state.claim)) state block (by
      intro witness member
      exact (Finset.mem_filter.mp member).2)
  apply bounded.trans
  gcongr
  exact Finset.filter_subset _ _

/-- ANY specific lift whose folded target has the running claim inherits that
claim outside the separately charged guarded round event. -/
theorem backward_claim (candidates : Finset (Array F)) (state : VerifierState F)
    (block lanes : Nat) (r : F) (next : Message F)
    (witness : Array F) (member : witness ∈ candidates)
    (shape : witness.size = (lanes * 2) * block) (weightShape : state.weight.size = witness.size)
    (safe : r ∉ candidateRoundEscape candidates state block)
    (targetClaim : dot (foldValues witness block r) (state.fold block r next).weight =
      (state.fold block r next).claim) : dot witness state.weight = state.claim := by
  by_contra falseClaim
  apply safe
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, witness, Finset.mem_filter.mpr ⟨member, falseClaim⟩, ?_⟩
  have fold := ArrayAlgebra.honest_foldLane witness state.weight block lanes shape weightShape r
  rw [← ReplayRefinement.foldValues_eq_lane, ← ReplayRefinement.foldValues_eq_lane] at fold
  exact fold.trans targetClaim

variable {I : Type*}

inductive SafeClaimFoldSchedule {k : Nat} (top : Bool)
    (enc : (Fin k → F) →ₗ[F] (I → F)) (C : Submodule F (I → F)) (threshold : Nat) :
    {start finish : Nat} → (Fin start → I → F) → (Fin finish → I → F) →
      VerifierState F → VerifierState F → (Array F → Array F) → Prop
  | done {lanes : Nat} (oracle : Fin lanes → I → F) (state : VerifierState F) :
      SafeClaimFoldSchedule top enc C threshold oracle oracle state state id
  | step {lanes finish : Nat} (oracle : Fin (lanes * 2) → I → F)
      (state : VerifierState F) (r : F) (next : Message F)
      (weightShape : state.weight.size = (lanes * 2) * k)
      (good : ¬ MutualAgreement.RowBad MutualAgreement.foldGenerator C threshold
        ![fun lane => oracle (evenLane lane), fun lane => oracle (oddLane lane)] r)
      (claimSafe : r ∉ candidateRoundEscape (arrayCandidates top enc oracle threshold)
        state (foldBlock top k))
      {last : Fin finish → I → F} {endState : VerifierState F} {transform : Array F → Array F}
      (rest : SafeClaimFoldSchedule top enc C threshold (foldOracle oracle r) last
        (state.fold (foldBlock top k) r next) endState transform) :
      SafeClaimFoldSchedule top enc C threshold oracle last state endState
        (fun a => transform (foldValues a (foldBlock top k) r))

/-- SAME-target lifting with candidate-specific claim preservation through
every actual compact round. No honest message is required. -/
theorem same_target_claim_lifts {k start finish : Nat} (top : Bool)
    (enc : (Fin k → F) →ₗ[F] (I → F)) (C : Submodule F (I → F))
    (rangeEq : LinearMap.range enc = C) (threshold : Nat)
    (oracle : Fin start → I → F) (last : Fin finish → I → F)
    (state endState : VerifierState F) (transform : Array F → Array F)
    (schedule : SafeClaimFoldSchedule top enc C threshold oracle last state endState transform)
    (target : Array F) (member : target ∈ arrayCandidates top enc last threshold)
    (targetClaim : dot target endState.weight = endState.claim) :
    ∃ original ∈ arrayCandidates top enc oracle threshold,
      transform original = target ∧ dot original state.weight = state.claim := by
  induction schedule with
  | done oracle state => exact ⟨target, member, rfl, targetClaim⟩
  | @step lanes finish oracle state r next weightShape good claimSafe last endState transform rest ih =>
    obtain ⟨middle, hmiddle, hequal, hclaim⟩ := ih member targetClaim
    obtain ⟨original, horiginal, hfold⟩ := array_lifts top enc C rangeEq oracle threshold r good middle hmiddle
    refine ⟨original, horiginal, by simpa only [← hfold] using hequal, ?_⟩
    apply backward_claim (arrayCandidates top enc oracle threshold) state (foldBlock top k)
      (if top then lanes else lanes * k) r next original horiginal
      (arrayCandidates_round_shape top enc oracle threshold original horiginal)
      (weightShape.trans (arrayCandidates_size top enc oracle threshold original horiginal).symm)
      claimSafe
    simpa only [← hfold] using hclaim

/-- The separately charged initial batching event transfers a TRUE batched
claim of the very lifted candidate to ALL original public claims. -/
theorem all_claims_of_safe_batch (candidates : Finset (Array E)) (claims : Array CausalGame.Claim)
    (lambda : E) (original : Array E) (member : original ∈ candidates)
    (safe : lambda ∉ InitialBatching.candidateEscape candidates claims)
    (batched : dot original (CausalGame.batchClaims original.size claims lambda).weight =
      (CausalGame.batchClaims original.size claims lambda).value) :
    ∀ claim ∈ claims.toList, dot original claim.weight = claim.value := by
  classical
  have each : ∀ j : Fin claims.size, dot original claims[j].weight = claims[j].value := by
    intro j
    by_contra falseClaim
    apply safe
    apply Finset.mem_biUnion.mpr
    refine ⟨original, member, ?_⟩
    simp only [InitialBatching.escape, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨j, falseClaim⟩, batched⟩
  intro claim memberClaim
  obtain ⟨j, hj, equal⟩ := List.mem_iff_getElem.mp memberClaim
  have bound : j < claims.size := by simpa using hj
  have result := each ⟨j, bound⟩
  change dot original claims[j].weight = claims[j].value at result
  simpa only [← equal, Array.getElem_toList] using result

#print axioms candidateRoundEscape_probability
#print axioms backward_claim
end Whir.SupportedCandidateExtraction
