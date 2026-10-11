import Whir.ArrayAlgebra
import Whir.ReplayRefinement
import Whir.Soundness

/-! The lost invariant is about arbitrary received messages, not honest-prover
traces. Candidate lifting is separated from polynomial collision events so the
coding-theoretic obligation cannot disappear inside a composition hypothesis. -/
namespace Whir.VerifierInvariant
open Concrete Protocol Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [CharP F 2]

/-- The polynomial represented by the actual transmitted pair and running claim. -/
noncomputable def messagePolynomial (message : Message F) (claim : F) : F[X] :=
  C message.u2 * X ^ 2 + C (claim + message.u2) * X + C message.u0

omit [Fintype F] [DecidableEq F] [Inhabited F] [CharP F 2] in
@[simp] theorem messagePolynomial_eval (message : Message F) (claim r : F) :
    (messagePolynomial message claim).eval r = message.eval claim r := by
  simp only [messagePolynomial, eval_add, eval_mul, eval_pow, eval_C, eval_X, Message.eval]
  ring

omit [Fintype F] [DecidableEq F] [Inhabited F] [CharP F 2] in
theorem messagePolynomial_degree (message : Message F) (claim : F) :
    (messagePolynomial message claim).natDegree ≤ 2 := natDegree_quadratic_le

omit [Fintype F] [DecidableEq F] [Inhabited F] in
theorem messagePolynomial_endpoints (message : Message F) (claim : F) :
    (messagePolynomial message claim).eval 0 + (messagePolynomial message claim).eval 1 = claim := by
  simp only [messagePolynomial_eval, ArrayAlgebra.message_eval]
  exact Whir.compactRound_endpoints claim message.u0 message.u2

/-- Every commitment-fixed candidate violates the current weighted claim. -/
def Lost (candidates : Finset (Array F)) (state : VerifierState F) : Prop :=
  ∀ witness ∈ candidates, dot witness state.weight ≠ state.claim

noncomputable def roundBad (candidates : Finset (Array F)) (state : VerifierState F)
    (block : Nat) : Finset F := by
  classical
  exact Finset.univ.filter fun r => ∃ witness ∈ candidates,
    (roundMessage witness state.weight block).eval (dot witness state.weight) r =
      state.message.eval state.claim r

omit [Fintype F] [DecidableEq F] in
/-- A false running claim forces distinct polynomials even for a malicious intro. -/
theorem false_candidate_polynomials (state : VerifierState F) (witness : Array F)
    (block : Nat) (falseClaim : dot witness state.weight ≠ state.claim) :
    messagePolynomial (roundMessage witness state.weight block) (dot witness state.weight) ≠
      messagePolynomial state.message state.claim := by
  apply Soundness.false_claim_distinct _ _ state.claim
  · simpa only [messagePolynomial_endpoints] using falseClaim
  · exact messagePolynomial_endpoints _ _

/-- Actual compressed-message collisions cost at most two roots per candidate. -/
theorem roundBad_probability (candidates : Finset (Array F)) (state : VerifierState F)
    (block : Nat) (lost : Lost candidates state) :
    Soundness.uniformProb (roundBad candidates state block) ≤
      (candidates.card : ℚ) * (2 / (Fintype.card F : ℚ)) := by
  classical
  let events : candidates → Finset F := fun witness => Finset.univ.filter fun r =>
    (messagePolynomial (roundMessage witness.val state.weight block)
      (dot witness.val state.weight)).eval r =
      (messagePolynomial state.message state.claim).eval r
  have heq : roundBad candidates state block = Finset.univ.biUnion events := by
    ext r
    simp [roundBad, events]
  rw [heq]
  calc
    _ ≤ ∑ witness : candidates, Soundness.uniformProb (events witness) := Soundness.union_bound events
    _ ≤ ∑ _witness : candidates, (2 : ℚ) / Fintype.card F := by
      apply Finset.sum_le_sum
      intro witness _
      exact Soundness.round_error _ _
        (false_candidate_polynomials state witness.val block (lost _ witness.property)) 2
        (messagePolynomial_degree _ _) (messagePolynomial_degree _ _)
    _ = _ := by simp

/-- The next pending message is arbitrary. Only list lifting and avoidance of the
explicit root event are needed for preservation through the actual fold helper. -/
theorem fold_lost (oldCandidates newCandidates : Finset (Array F))
    (state : VerifierState F) (block lanes : Nat) (r : F) (next : Message F)
    (shape : ∀ witness ∈ oldCandidates, witness.size = (lanes * 2) * block)
    (weights : ∀ witness ∈ oldCandidates, state.weight.size = witness.size)
    (lifts : ∀ folded ∈ newCandidates, ∃ witness ∈ oldCandidates,
      folded = foldValues witness block r)
    (outside : r ∉ roundBad oldCandidates state block) :
    Lost newCandidates (state.fold block r next) := by
  intro folded hfolded heq
  obtain ⟨witness, hwitness, rfl⟩ := lifts folded hfolded
  apply outside
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, witness, hwitness, ?_⟩
  rw [show (roundMessage witness state.weight block).eval (dot witness state.weight) r =
      dot (foldValues witness block r) (foldValues state.weight block r) by
    simp only [ReplayRefinement.foldValues_eq_lane]
    exact ArrayAlgebra.honest_foldLane witness state.weight block lanes
      (shape witness hwitness) (weights witness hwitness) r]
  exact heq

end Whir.VerifierInvariant
