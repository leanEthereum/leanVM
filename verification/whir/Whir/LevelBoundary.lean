import Whir.FieldTower
import Whir.ExecutableOOD
import Whir.SamplingProbability
import Whir.VerifierInvariant
import Whir.CandidateFolding

/-! At the level boundary the OOD response selects at most one new candidate
before the entire query-vector/adjacent-lambda message. This is the reason the
query error has no candidate-list factor. -/
namespace Whir.LevelBoundary
open Concrete Protocol

abbrev QueryTape (depth count : Nat) :=
  Fin ((count + 192 / depth - 1) / (192 / depth)) → E

noncomputable def agreeingColumns (n rate : Nat) (witness : Array E)
    (oldWord : Fin (2 ^ (n + rate)) → E) : Finset (Fin (2 ^ (n + rate))) := by
  classical
  exact Finset.univ.filter fun q => (encode n rate witness)[q.val]! = oldWord q

/-- A single-row post-fold oracle's list violates the residual claim. -/
def CloseLost (n rate threshold : Nat) (oldWord : Fin (2 ^ (n + rate)) → E)
    (state : VerifierState E) : Prop :=
  ∀ witness : Array E, witness.size = 2 ^ n →
    threshold ≤ (agreeingColumns n rate witness oldWord).card →
      dot witness state.weight ≠ state.claim

/-- The actual one-lane candidate list gives the close invariant directly. -/
theorem closeLost_of_lost (top : Bool) (n rate threshold : Nat)
    (oldWord : Fin (2 ^ (n + rate)) → E) (state : VerifierState E)
    (lost : VerifierInvariant.Lost
      (CandidateFolding.arrayCandidates top (CandidateFolding.concreteEncoder n rate)
        (fun _ : Fin 1 => oldWord) threshold) state) :
    CloseLost n rate threshold oldWord state := by
  intro witness shape agreement
  apply lost witness
  exact (CandidateFolding.concrete_oneLane_mem_iff top n rate threshold oldWord witness).mpr
    ⟨shape, agreement⟩

def Separated (candidates : Finset (Array E)) (point : Array E) : Prop :=
  ∀ left ∈ candidates, ∀ right ∈ candidates,
    Concrete.mle left point = Concrete.mle right point → left = right

/-- A candidate survives every residual, OOD and sampled-column claim. The rows
here are determined by the old oracle, not by a post-lambda response. -/
noncomputable def queryEscape (n rate count : Nat)
    (oldWord : Fin (2 ^ (n + rate)) → E) (state : VerifierState E)
    (candidates : Finset (Array E)) (point : Array E) (answer : E) :
    Finset (QueryTape (n + rate) count) := by
  classical
  exact Finset.univ.filter fun tape => ∃ witness ∈ candidates,
    Concrete.mle witness point = answer ∧ dot witness state.weight = state.claim ∧
    SamplingProbability.allQueriesHit (n + rate) count
      (agreeingColumns n rate witness oldWord) tape

open Classical in
/-- The OOD-separation event is bounded for the actual array MLE. -/
theorem separation_probability (n : Nat) (candidates : Finset (Array E))
    (sizes : ∀ witness ∈ candidates, witness.size = 2 ^ n) :
    Soundness.uniformProb (Finset.univ.filter fun point : Fin n → E =>
      ¬ Separated candidates (Array.ofFn point)) ≤
      (candidates.card.choose 2 : ℚ) * ((n : ℚ) / Fintype.card E) := by
  classical
  have event : (Finset.univ.filter fun point : Fin n → E =>
      ¬ Separated candidates (Array.ofFn point)) =
      (Finset.univ.filter fun point : Fin n → E =>
        ∃ left ∈ candidates, ∃ right ∈ candidates, left ≠ right ∧
          Concrete.mle left (Array.ofFn point) = Concrete.mle right (Array.ofFn point)) := by
    ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hn
      apply h
      intro left hl right hr heq
      by_contra hne
      exact hn ⟨left, hl, right, hr, hne, heq⟩
    · rintro ⟨left, hl, right, hr, hne, heq⟩ hsep
      exact hne (hsep left hl right hr heq)
  rw [event]
  exact ExecutableOOD.candidate_separation candidates sizes

/-- Exact actual sampler bound at a separated OOD boundary. All inputs outside
`tape` are fixed before queries; no iid sampling or list-union assumption is used. -/
theorem query_escape_probability (n rate count threshold : Nat)
    (oldWord : Fin (2 ^ (n + rate)) → E) (state : VerifierState E)
    (candidates : Finset (Array E)) (point : Array E) (answer : E)
    (alpha : ℚ) (alpha_nonneg : 0 ≤ alpha)
    (threshold_eq : threshold = ⌈(2 ^ (n + rate) : ℚ) * alpha⌉₊)
    (depth_pos : 0 < n + rate) (depth_bound : n + rate ≤ 64)
    (sizes : ∀ witness ∈ candidates, witness.size = 2 ^ n)
    (lost : CloseLost n rate threshold oldWord state)
    (separated : Separated candidates point) :
    Soundness.uniformProb (queryEscape n rate count oldWord state candidates point answer) ≤
      alpha ^ count := by
  classical
  by_cases existsCandidate : ∃ witness ∈ candidates,
      Concrete.mle witness point = answer ∧ dot witness state.weight = state.claim
  · obtain ⟨witness, hw, hpoint, hclaim⟩ := existsCandidate
    have unique : ∀ other ∈ candidates, Concrete.mle other point = answer → other = witness := by
      intro other ho hp
      exact separated other ho witness hw (hp.trans hpoint.symm)
    have small : (agreeingColumns n rate witness oldWord).card < threshold := by
      apply Nat.lt_of_not_ge
      intro close
      exact lost witness (sizes witness hw) close hclaim
    have density : ((agreeingColumns n rate witness oldWord).card : ℚ) /
        (2 ^ (n + rate) : ℚ) ≤ alpha := by
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (n + rate))).mpr
      rw [threshold_eq] at small
      have h := Nat.lt_ceil.mp small
      nlinarith
    have event : queryEscape n rate count oldWord state candidates point answer =
        Finset.univ.filter (SamplingProbability.allQueriesHit (n + rate) count
          (agreeingColumns n rate witness oldWord)) := by
      ext tape
      simp only [queryEscape, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨other, ho, hp, _, hits⟩
        simpa only [unique other ho hp] using hits
      · intro hits
        exact ⟨witness, hw, hpoint, hclaim, hits⟩
    rw [event]
    have sampled := SamplingProbability.actual_query_bound_rat
      (n + rate) count depth_pos depth_bound (agreeingColumns n rate witness oldWord)
    simp only [Nat.cast_pow, Nat.cast_ofNat] at sampled
    exact sampled.trans (pow_le_pow_left₀ (by positivity) density count)
  · have empty : queryEscape n rate count oldWord state candidates point answer = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro tape h
      obtain ⟨witness, hw, hp, hc, _⟩ := (Finset.mem_filter.mp h).2
      exact existsCandidate ⟨witness, hw, hp, hc⟩
    rw [empty]
    simp only [Soundness.uniformProb, Finset.card_empty, Nat.cast_zero, zero_div]
    exact pow_nonneg alpha_nonneg count

end Whir.LevelBoundary
