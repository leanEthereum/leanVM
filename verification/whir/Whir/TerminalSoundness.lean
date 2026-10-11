import Whir.VerifierInvariant
import Whir.TerminalRefinement
import Whir.OperationalRefinement
import Whir.FieldTower

/-! Adversarial closing soundness for the executable verifier. The residual is
one fixed candidate, while every pending message (including the incoming one)
is arbitrary. The only exceptional challenges are actual quadratic collisions.
No acceptance or honest-message premise is used by the rejection theorem. -/
namespace Whir.TerminalSoundness
open Concrete Protocol ArrayAlgebra ArrayLayout VerifierInvariant

/-- Actual verifier state immediately before closing round `j`. -/
def stateAt (ch : Challenges) (proof : Opening) (s : VerifierState E) (j : Nat) :
    VerifierState E := runSteps (tailStep ch proof) j 0 s

/-- The commitment-fixed residual after the same adjacent-pair folds. -/
def residualAt (ch : Challenges) (residual : Array E) (j : Nat) : Array E :=
  runSteps (fun i a => foldLow a ch.tail[i]!) j 0 residual

private theorem runSteps_add {S : Type*} (step : Nat → S → S)
    (a b start : Nat) (s : S) :
    runSteps step (a+b) start s = runSteps step b (start+a) (runSteps step a start s) := by
  induction a generalizing start s with
  | zero => simp [runSteps]
  | succ a ih =>
    simpa [runSteps, Nat.succ_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (start+1) (step start s)

private theorem runSteps_succ_last {S : Type*} (step : Nat → S → S) (j : Nat) (s : S) :
    runSteps step (j+1) 0 s = step j (runSteps step j 0 s) := by
  rw [runSteps_add]
  simp [runSteps]

@[simp] theorem stateAt_zero (ch : Challenges) (proof : Opening) (s : VerifierState E) :
    stateAt ch proof s 0 = s := rfl

@[simp] theorem stateAt_succ (ch : Challenges) (proof : Opening) (s : VerifierState E) (j : Nat) :
    stateAt ch proof s (j+1) = tailStep ch proof j (stateAt ch proof s j) :=
  runSteps_succ_last _ _ _

@[simp] theorem residualAt_zero (ch : Challenges) (a : Array E) : residualAt ch a 0 = a := rfl

@[simp] theorem residualAt_succ (ch : Challenges) (a : Array E) (j : Nat) :
    residualAt ch a (j+1) = foldLow (residualAt ch a j) ch.tail[j]! :=
  runSteps_succ_last _ _ _

/-- Power-of-two sizes evolve along the actual residual folds. -/
theorem residualAt_size (ch : Challenges) (a : Array E)
    (shape : a.size = 2 ^ ch.tail.size) (j : Nat) (hj : j ≤ ch.tail.size) :
    (residualAt ch a j).size = 2 ^ (ch.tail.size-j) := by
  induction j with
  | zero => simpa using shape
  | succ j ih =>
    rw [residualAt_succ, size_foldLow, ih (by omega)]
    have h : ch.tail.size-j = (ch.tail.size-(j+1))+1 := by omega
    rw [h, pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]

/-- Verifier weights follow precisely the same executable folds, independently
of the claims and all supplied messages. -/
theorem stateAt_weight (ch : Challenges) (proof : Opening) (s : VerifierState E) (j : Nat) :
    (stateAt ch proof s j).weight = residualAt ch s.weight j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [tailStep, VerifierState.fold, foldValues, ih]

theorem stateAt_weight_size (ch : Challenges) (proof : Opening) (s : VerifierState E)
    (shape : s.weight.size = 2 ^ ch.tail.size) (j : Nat) (hj : j ≤ ch.tail.size) :
    (stateAt ch proof s j).weight.size = 2 ^ (ch.tail.size-j) := by
  rw [stateAt_weight]
  exact residualAt_size ch s.weight shape j hj

/-- Explicit singleton collision event for a fixed prior transcript. -/
noncomputable def collision (a : Array E) (s : VerifierState E) : Finset E :=
  roundBad {a} s 1

theorem collision_probability (a : Array E) (s : VerifierState E)
    (falseClaim : dot a s.weight ≠ s.claim) :
    Soundness.uniformProb (collision a s) ≤ 2 / (Fintype.card E : ℚ) := by
  have lost : Lost {a} s := by simpa [Lost] using falseClaim
  simpa [collision] using roundBad_probability {a} s 1 lost

/-- Avoiding the explicit event preserves falsity for any next message. -/
theorem fold_false (a : Array E) (s : VerifierState E) (pairs : Nat) (r : E)
    (next : Message E) (shape : a.size = pairs*2) (weights : s.weight.size = a.size)
    (outside : r ∉ collision a s) :
    dot (foldLow a r) (s.fold 1 r next).weight ≠ (s.fold 1 r next).claim := by
  have h : Lost {foldLow a r} (s.fold 1 r next) := by
    apply fold_lost {a} {foldLow a r} s 1 pairs r next
    · simpa using shape
    · simpa using weights
    · simp [foldValues]
    · exact outside
  simpa [Lost] using h

/-- At every prefix the candidate and weights retain their exact lengths, and
falsity persists without any honesty condition on the opening messages. -/
theorem closing_false (ch : Challenges) (proof : Opening) (s : VerifierState E)
    (shape : proof.residual.size = 2 ^ ch.tail.size)
    (weights : s.weight.size = proof.residual.size)
    (falseClaim : dot proof.residual s.weight ≠ s.claim)
    (avoid : ∀ j < ch.tail.size, ch.tail[j]! ∉
      collision (residualAt ch proof.residual j) (stateAt ch proof s j))
    (j : Nat) (hj : j ≤ ch.tail.size) :
    dot (residualAt ch proof.residual j) (stateAt ch proof s j).weight ≠
      (stateAt ch proof s j).claim := by
  induction j with
  | zero => exact falseClaim
  | succ j ih =>
    rw [residualAt_succ, stateAt_succ]
    unfold tailStep
    apply fold_false _ _ (2^(ch.tail.size-(j+1)))
    · rw [residualAt_size ch proof.residual shape j (by omega)]
      rw [show ch.tail.size-j = (ch.tail.size-(j+1))+1 by omega, pow_succ]
    · rw [stateAt_weight_size ch proof s (weights.trans shape) j (by omega),
        residualAt_size ch proof.residual shape j (by omega)]
    · exact avoid j (by omega)

/-- Identification uses the actual array-order terminal refinement, rather than
assuming equality to a supplied final scalar. -/
theorem residualAt_terminal (ch : Challenges) (a : Array E)
    (shape : a.size = 2 ^ ch.tail.size) :
    residualAt ch a ch.tail.size = #[Concrete.mle a ch.tail] := by
  have mapped : (List.range ch.tail.size).map (fun i => ch.tail[i]!) = ch.tail.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      simp only [getElem!_pos ch.tail i (by simpa using hi')]
  rw [residualAt, OperationalRefinement.runSteps_eq_foldl, ← List.range_eq_range']
  change (List.range ch.tail.size).foldl (fun a i => foldLow a ch.tail[i]!) a = _
  rw [← List.foldl_map, mapped, Array.foldl_toList]
  exact TerminalRefinement.foldLow_terminal a ch.tail shape

/-- False terminal singleton claims reject through the actual residual MLE check. -/
theorem checkClosing_rejects_of_terminal_false (ch : Challenges) (proof : Opening)
    (s : VerifierState E) (shape : proof.residual.size = 2 ^ ch.tail.size)
    (weights : s.weight.size = proof.residual.size)
    (h : dot (residualAt ch proof.residual ch.tail.size)
      (stateAt ch proof s ch.tail.size).weight ≠ (stateAt ch proof s ch.tail.size).claim) :
    checkClosing ch proof (closeTail ch proof s) = .error "terminal mismatch" := by
  rw [residualAt_terminal ch proof.residual shape] at h
  have hw := stateAt_weight_size ch proof s (weights.trans shape) ch.tail.size le_rfl
  simp only [Nat.sub_self, pow_zero] at hw
  have hdot : dot #[Concrete.mle proof.residual ch.tail]
      (stateAt ch proof s ch.tail.size).weight =
      Concrete.mle proof.residual ch.tail * (stateAt ch proof s ch.tail.size).weight[0]! := by
    simp [dot_eq_sum, hw]
  rw [hdot] at h
  have bad : (closeTail ch proof s).checkTerminal (Concrete.mle proof.residual ch.tail) = false := by
    simpa [VerifierState.checkTerminal, closeTail, stateAt, ne_comm] using h
  simp only [checkClosing, bad, Bool.not_false, ite_true]
  rfl

/-- An arbitrary adversarial closing transcript must be rejected if its incoming
weighted residual claim is false and none of its actual quadratic events occurs. -/
theorem checkClosing_rejects (ch : Challenges) (proof : Opening) (s : VerifierState E)
    (shape : proof.residual.size = 2 ^ ch.tail.size)
    (weights : s.weight.size = proof.residual.size)
    (falseClaim : dot proof.residual s.weight ≠ s.claim)
    (avoid : ∀ j < ch.tail.size, ch.tail[j]! ∉
      collision (residualAt ch proof.residual j) (stateAt ch proof s j)) :
    checkClosing ch proof (closeTail ch proof s) = .error "terminal mismatch" :=
  checkClosing_rejects_of_terminal_false ch proof s shape weights
    (closing_false ch proof s shape weights falseClaim avoid ch.tail.size le_rfl)

/-- Two actual roots at most, for every fixed adversarial pending message. -/
theorem collision_card (a : Array E) (s : VerifierState E)
    (falseClaim : dot a s.weight ≠ s.claim) : (collision a s).card ≤ 2 := by
  have h := Soundness.evaluation_agreement (Finset.univ : Finset E)
    (messagePolynomial (roundMessage a s.weight 1) (dot a s.weight))
    (messagePolynomial s.message s.claim)
    (false_candidate_polynomials s a 1 falseClaim) 2
    (messagePolynomial_degree _ _) (messagePolynomial_degree _ _)
  simpa [collision, roundBad] using h

/-- Finite conditional counting: the arbitrary state and candidate may depend on
all prior history, but not on the fresh field element. Histories at which the
claim is already true are not charged as an escape. -/
theorem conditional_collision_count {History : Type*} [Fintype History]
    (candidate : History → Array E) (state : History → VerifierState E) :
    (Finset.univ.filter fun hr : History × E =>
      dot (candidate hr.1) (state hr.1).weight ≠ (state hr.1).claim ∧
      hr.2 ∈ collision (candidate hr.1) (state hr.1)).card ≤ Fintype.card History * 2 := by
  classical
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  calc
    _ ≤ ∑ h : History, 2 := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hf : dot (candidate h) (state h).weight ≠ (state h).claim
      · simpa [hf, ← Finset.card_filter] using collision_card (candidate h) (state h) hf
      · simp [hf]
    _ = _ := by simp

/-- The fixed-history two-root estimate survives arbitrary finite conditioning
on prior transcripts. The fresh challenge is the independent product factor. -/
theorem conditional_collision_probability {History : Type*} [Fintype History]
    [Nonempty History] (candidate : History → Array E) (state : History → VerifierState E) :
    Soundness.uniformProb (Finset.univ.filter fun hr : History × E =>
      dot (candidate hr.1) (state hr.1).weight ≠ (state hr.1).claim ∧
      hr.2 ∈ collision (candidate hr.1) (state hr.1)) ≤ 2 / (Fintype.card E : ℚ) := by
  classical
  unfold Soundness.uniformProb
  rw [Fintype.card_prod, Nat.cast_mul]
  have hp : (0 : ℚ) < Fintype.card History := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ ((Fintype.card History : ℚ) * 2) /
        ((Fintype.card History : ℚ) * Fintype.card E) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast conditional_collision_count candidate state
    _ = _ := by field_simp

/-- Actual acceptance of a false incoming claim exposes a first quadratic
collision while the residual weighted claim is still false. -/
theorem accepted_has_collision (ch : Challenges) (proof : Opening) (s : VerifierState E)
    (shape : proof.residual.size = 2 ^ ch.tail.size)
    (weights : s.weight.size = proof.residual.size)
    (falseClaim : dot proof.residual s.weight ≠ s.claim)
    (accepted : checkClosing ch proof (closeTail ch proof s) = .ok ()) :
    ∃ j < ch.tail.size,
      dot (residualAt ch proof.residual j) (stateAt ch proof s j).weight ≠
        (stateAt ch proof s j).claim ∧
      ch.tail[j]! ∈ collision (residualAt ch proof.residual j) (stateAt ch proof s j) := by
  classical
  let lost := fun j => dot (residualAt ch proof.residual j) (stateAt ch proof s j).weight ≠
    (stateAt ch proof s j).claim
  have initial : lost 0 := falseClaim
  have final : ¬ lost ch.tail.size := by
    intro h
    have bad := checkClosing_rejects_of_terminal_false ch proof s shape weights h
    rw [bad] at accepted
    contradiction
  obtain ⟨j, hj, hl, hn⟩ := Soundness.first_escape lost ch.tail.size initial final
  refine ⟨j, hj, hl, ?_⟩
  by_contra outside
  apply hn
  dsimp only [lost]
  rw [residualAt_succ, stateAt_succ]
  unfold tailStep
  apply fold_false _ _ (2^(ch.tail.size-(j+1)))
  · rw [residualAt_size ch proof.residual shape j (by omega)]
    rw [show ch.tail.size-j = (ch.tail.size-(j+1))+1 by omega, pow_succ]
  · rw [stateAt_weight_size ch proof s (weights.trans shape) j (by omega),
      residualAt_size ch proof.residual shape j (by omega)]
  · exact outside

/-- Finite causal composition for actual closing executions. Each `split` exposes
the fresh independent field coordinate; the two causality equations require
the candidate and pending verifier state to be fixed without that coordinate.
No local or global probability bound is assumed. -/
theorem causal_closing_bound {Ω History : Type*} [Fintype Ω] [Fintype History]
    [Nonempty History] (n : Nat)
    (ch : Ω → Challenges) (proof : Ω → Opening) (s : Ω → VerifierState E)
    (lengths : ∀ ω, (ch ω).tail.size = n)
    (shape : ∀ ω, (proof ω).residual.size = 2 ^ (ch ω).tail.size)
    (weights : ∀ ω, (s ω).weight.size = (proof ω).residual.size)
    (falseClaim : ∀ ω, dot (proof ω).residual (s ω).weight ≠ (s ω).claim)
    (split : Fin n → Ω ≃ (History × E))
    (candidate : Fin n → History → Array E)
    (prior : Fin n → History → VerifierState E)
    (candidate_causal : ∀ (i : Fin n) ω,
      residualAt (ch ω) (proof ω).residual i = candidate i (split i ω).1)
    (state_causal : ∀ (i : Fin n) ω,
      stateAt (ch ω) (proof ω) (s ω) i = prior i (split i ω).1)
    (fresh : ∀ (i : Fin n) ω, (ch ω).tail[i.val]! = (split i ω).2) :
    Soundness.uniformProb (Finset.univ.filter fun ω =>
      checkClosing (ch ω) (proof ω) (closeTail (ch ω) (proof ω) (s ω)) = .ok ()) ≤
      (n : ℚ) * (2 / (Fintype.card E : ℚ)) := by
  classical
  let event : Fin n → Finset Ω := fun i => Finset.univ.filter fun ω =>
    dot (candidate i (split i ω).1) (prior i (split i ω).1).weight ≠
      (prior i (split i ω).1).claim ∧
    (split i ω).2 ∈ collision (candidate i (split i ω).1) (prior i (split i ω).1)
  have sub : (Finset.univ.filter fun ω =>
      checkClosing (ch ω) (proof ω) (closeTail (ch ω) (proof ω) (s ω)) = .ok ()) ⊆
      Finset.univ.biUnion event := by
    intro ω hω
    obtain ⟨j, hj, h⟩ := accepted_has_collision (ch ω) (proof ω) (s ω)
      (shape ω) (weights ω) (falseClaim ω) (Finset.mem_filter.mp hω).2
    let i : Fin n := ⟨j, by simpa [lengths ω] using hj⟩
    change dot (residualAt (ch ω) (proof ω).residual i)
      (stateAt (ch ω) (proof ω) (s ω) i).weight ≠
        (stateAt (ch ω) (proof ω) (s ω) i).claim ∧
      (ch ω).tail[i.val]! ∈ collision (residualAt (ch ω) (proof ω).residual i)
        (stateAt (ch ω) (proof ω) (s ω) i) at h
    rw [candidate_causal, state_causal, fresh] at h
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h⟩⟩
  have bounded (i : Fin n) : Soundness.uniformProb (event i) ≤ 2 / (Fintype.card E : ℚ) := by
    have count : (event i).card = (Finset.univ.filter fun hr : History × E =>
        dot (candidate i hr.1) (prior i hr.1).weight ≠ (prior i hr.1).claim ∧
        hr.2 ∈ collision (candidate i hr.1) (prior i hr.1)).card := by
      simp only [event, Finset.card_filter]
      exact Equiv.sum_comp (split i) (fun hr : History × E =>
        if dot (candidate i hr.1) (prior i hr.1).weight ≠ (prior i hr.1).claim ∧
          hr.2 ∈ collision (candidate i hr.1) (prior i hr.1) then (1 : Nat) else 0)
    unfold Soundness.uniformProb
    rw [count, Fintype.card_congr (split i)]
    exact conditional_collision_probability (candidate i) (prior i)
  calc
    _ ≤ Soundness.uniformProb (Finset.univ.biUnion event) := by
      unfold Soundness.uniformProb
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card sub
    _ ≤ ∑ i, Soundness.uniformProb (event i) := Soundness.union_bound event
    _ ≤ ∑ _i : Fin n, 2 / (Fintype.card E : ℚ) :=
      Finset.sum_le_sum (fun i _ => bounded i)
    _ = _ := by simp

end Whir.TerminalSoundness
