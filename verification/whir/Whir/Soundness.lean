module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section

namespace Whir.Soundness

open scoped BigOperators
open Polynomial

/-- Exact probability under the uniform distribution on a finite sample space. -/
def uniformProb {Ω : Type*} [Fintype Ω] (event : Finset Ω) : ℚ :=
  (event.card : ℚ) / Fintype.card Ω

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A challenge is sampled after the nonzero error polynomial is fixed. -/
theorem root_count (p : F[X]) (hp : p ≠ 0) :
    (Finset.univ.filter (fun x => p.eval x = 0)).card ≤ p.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  exact (Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp hx).2

theorem root_error (p : F[X]) (hp : p ≠ 0) (d : ℕ) (hd : p.natDegree ≤ d) :
    uniformProb (Finset.univ.filter (fun x => p.eval x = 0)) ≤
      (d : ℚ) / Fintype.card F := by
  unfold uniformProb
  exact div_le_div_of_nonneg_right (by exact_mod_cast (root_count p hp).trans hd)
    (by positivity)

/-- An adaptive prover may choose the error from any finite prior history. The new
challenge is independent and uniform, represented by the product sample space. -/
theorem adaptive_root_count {History : Type*} [Fintype History]
    (errors : History → F[X]) (d : ℕ) (nonzero : ∀ h, errors h ≠ 0)
    (degrees : ∀ h, (errors h).natDegree ≤ d) :
    (Finset.univ.filter (fun hr : History × F => (errors hr.1).eval hr.2 = 0)).card ≤
      Fintype.card History * d := by
  classical
  have count :
      (Finset.univ.filter (fun hr : History × F => (errors hr.1).eval hr.2 = 0)).card =
        ∑ h : History, (Finset.univ.filter fun r => (errors h).eval r = 0).card := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [count]
  calc
    _ ≤ ∑ _h : History, d :=
      Finset.sum_le_sum (fun h _ => (root_count _ (nonzero h)).trans (degrees h))
    _ = _ := by simp

/-- Distinct round polynomials have at most d accepting challenges. -/
theorem round_error (honest sent : F[X]) (hne : honest ≠ sent)
    (d : ℕ) (hh : honest.natDegree ≤ d) (hs : sent.natDegree ≤ d) :
    uniformProb (Finset.univ.filter (fun r => honest.eval r = sent.eval r)) ≤
      (d : ℚ) / Fintype.card F := by
  have hp : honest - sent ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (honest - sent).natDegree ≤ d :=
    (natDegree_sub_le honest sent).trans (max_le hh hs)
  simpa only [eval_sub, sub_eq_zero] using root_error (honest - sent) hp d hdeg

omit [Fintype F] in
/-- Distinct RS polynomials agree in at most their degree bound on any domain. -/
theorem evaluation_agreement (domain : Finset F) (p q : F[X]) (hne : p ≠ q)
    (d : ℕ) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    (domain.filter fun x => p.eval x = q.eval x).card ≤ d := by
  have hsub : (domain.filter fun x => p.eval x = q.eval x).val ⊆ (p - q).roots := by
    intro x hx
    apply (Polynomial.mem_roots (sub_ne_zero.mpr hne)).mpr
    change (p - q).eval x = 0
    simp only [eval_sub, sub_eq_zero]
    exact (Finset.mem_filter.mp hx).2
  exact (Polynomial.card_le_degree_of_subset_roots hsub).trans
    ((natDegree_sub_le p q).trans (max_le hp hq))

omit [Fintype F] in
/-- Absolute Reed-Solomon distance, before any relative-distance division. -/
theorem reed_solomon_distance (domain : Finset F) (p q : F[X]) (hne : p ≠ q)
    (d : ℕ) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    domain.card - d ≤ (domain.filter fun x => p.eval x ≠ q.eval x).card := by
  have ha := evaluation_agreement domain p q hne d hp hq
  have hc := Finset.card_filter_add_card_filter_not (s := domain) (fun x => p.eval x = q.eval x)
  change (domain.filter fun x => p.eval x = q.eval x).card +
    (domain.filter fun x => p.eval x ≠ q.eval x).card = domain.card at hc
  omega

omit [Fintype F] [DecidableEq F] in
/-- A false incoming sum forces an honest polynomial to differ from every accepted message. -/
theorem false_claim_distinct (honest sent : F[X]) (claim : F)
    (falseClaim : honest.eval 0 + honest.eval 1 ≠ claim)
    (acceptedMessage : sent.eval 0 + sent.eval 1 = claim) : honest ≠ sent := by
  intro h
  exact falseClaim (h ▸ acceptedMessage)

/-- The quadratic sumcheck round error, including characteristic two. -/
theorem sumcheck_round_error (honest sent : F[X]) (claim : F)
    (falseClaim : honest.eval 0 + honest.eval 1 ≠ claim)
    (acceptedMessage : sent.eval 0 + sent.eval 1 = claim)
    (hh : honest.natDegree ≤ 2) (hs : sent.natDegree ≤ 2) :
    uniformProb (Finset.univ.filter (fun r => honest.eval r = sent.eval r)) ≤
      (2 : ℚ) / Fintype.card F :=
  round_error honest sent (false_claim_distinct honest sent claim falseClaim acceptedMessage) 2 hh hs

/-- A nonzero coefficient witnesses that a batched error cannot vanish identically. -/
theorem batching_error (errors : F[X]) (i d : ℕ) (hi : errors.coeff i ≠ 0)
    (hd : errors.natDegree ≤ d) :
    uniformProb (Finset.univ.filter (fun r => errors.eval r = 0)) ≤
      (d : ℚ) / Fintype.card F := by
  apply root_error errors _ d hd
  intro h
  exact hi (by simp [h])

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- No independence assumption is required for a union bound. -/
theorem union_bound {I : Type*} [Fintype I] (events : I → Finset Ω) :
    uniformProb (Finset.univ.biUnion events) ≤ ∑ i, uniformProb (events i) := by
  classical
  unfold uniformProb
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_biUnion_le

/-- A finite list may contain many candidates; every candidate's error remains explicit. -/
theorem list_root_error {I : Type*} [Fintype I]
    (errors : I → F[X]) (d : ℕ) (nonzero : ∀ i, errors i ≠ 0)
    (degrees : ∀ i, (errors i).natDegree ≤ d) :
    uniformProb (Finset.univ.biUnion fun i => Finset.univ.filter fun r => (errors i).eval r = 0) ≤
      (Fintype.card I : ℚ) * ((d : ℚ) / Fintype.card F) := by
  classical
  calc
    _ ≤ ∑ i, uniformProb (Finset.univ.filter fun r => (errors i).eval r = 0) := union_bound _
    _ ≤ ∑ _i : I, (d : ℚ) / Fintype.card F :=
      Finset.sum_le_sum (fun i _ => root_error _ (nonzero i) d (degrees i))
    _ = _ := by simp

/-- First-escape decomposition for a deterministic adversary on a sampled randomness tape.
The invariant means the prover has lost. Prover transitions must preserve it; the caller
supplies bounds only for verifier escapes, not a target whole-protocol soundness bound. -/
theorem first_escape (lost : ℕ → Prop) [DecidablePred lost] (n : ℕ)
    (initial : lost 0) (final : ¬ lost n) :
    ∃ i < n, lost i ∧ ¬ lost (i + 1) := by
  induction n with
  | zero => exact (final initial).elim
  | succ n ih =>
    by_cases h : lost n
    · exact ⟨n, Nat.lt_succ_self n, h, final⟩
    · obtain ⟨i, hi, hl, hn⟩ := ih h
      exact ⟨i, Nat.lt_succ_of_lt hi, hl, hn⟩

/-- Round-by-round error accumulation, for arbitrary (including adaptive) transcripts. -/
theorem rbr_composition (n : ℕ) (lost : Ω → ℕ → Prop)
    [∀ ω, DecidablePred (lost ω)] (accepts : Ω → Prop) [DecidablePred accepts]
    (initial : ∀ ω, lost ω 0) (terminal : ∀ ω, lost ω n → ¬ accepts ω)
    (errors : Fin n → ℚ)
    (roundBounds : ∀ i : Fin n,
      uniformProb (Finset.univ.filter fun ω => lost ω i ∧ ¬ lost ω (i + 1)) ≤ errors i) :
    uniformProb (Finset.univ.filter accepts) ≤ ∑ i, errors i := by
  classical
  let events : Fin n → Finset Ω := fun i => Finset.univ.filter fun ω => lost ω i ∧ ¬ lost ω (i + 1)
  have sub : Finset.univ.filter accepts ⊆ Finset.univ.biUnion events := by
    intro ω hω
    have acc := (Finset.mem_filter.mp hω).2
    obtain ⟨i, hi, hl, hn⟩ := first_escape (lost ω) n (initial ω) (fun h => terminal ω h acc)
    exact Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hn⟩⟩
  calc
    _ ≤ uniformProb (Finset.univ.biUnion events) := by
      unfold uniformProb
      exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card sub) (by positivity)
    _ ≤ ∑ i, uniformProb (events i) := union_bound events
    _ ≤ ∑ i, errors i := Finset.sum_le_sum (fun i _ => roundBounds i)

omit [Fintype Ω] in
/-- Grinding conditions the tape: the denominator is the number of permitted tapes,
not the original sample-space size. This statement does not justify a ROM compiler. -/
theorem conditioned_bound (bad permitted : Finset Ω) (bound : ℕ) (h : bad.card ≤ bound) :
    ((bad ∩ permitted).card : ℚ) / permitted.card ≤ (bound : ℚ) / permitted.card := by
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast (Finset.card_le_card Finset.inter_subset_left).trans h) (by positivity)

/-- Ideal list binding is a relation, not unique binding or a BLAKE2 theorem. -/
def ListExplains {Commitment Message Claim : Type*}
    (candidates : Commitment → Finset Message) (satisfies : Message → Claim → Prop)
    (commitment : Commitment) (claims : List Claim) : Prop :=
  ∃ message ∈ candidates commitment, ∀ claim ∈ claims, satisfies message claim

/-- Quantified ideal-interactive list binding. The candidate list is chosen from
the commitment before the strategy and its opened claims. The experiment supplies
the actual verifier, rather than allowing the adversary to set an acceptance bit.
No theorem here asserts that WHIR or a concrete transcript satisfies this game. -/
noncomputable def ListBinding {Commitment Message Claim Strategy : Type*}
    (satisfies : Message → Claim → Prop)
    (verify : Commitment → Strategy → Ω → Bool)
    (claims : Commitment → Strategy → Ω → List Claim)
    (listBound : ℕ) (error : ℚ) : Prop := by
  classical
  exact ∀ commitment, ∃ candidates : Finset Message, candidates.card ≤ listBound ∧
    ∀ strategy, uniformProb (Finset.univ.filter fun tape =>
      verify commitment strategy tape = true ∧
      ¬ ∃ message ∈ candidates,
        ∀ claim ∈ claims commitment strategy tape, satisfies message claim) ≤ error

end Whir.Soundness
