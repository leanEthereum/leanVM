import SphincsSecurity.Proof.Forced.SecretGuessObservation
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def pairValue (rate : ENNReal) (remaining : Nat) : Nat → ENNReal
  | 0 => remaining.choose 2 * rate ^ 2
  | 1 => remaining * rate
  | _ + 2 => 1

theorem pairValue_mono (rate : ENNReal) (hits : Nat) {first second : Nat} (h : first ≤ second) :
    pairValue rate first hits ≤ pairValue rate second hits := by
  cases hits with
  | zero => exact mul_le_mul' (by exact_mod_cast Nat.choose_le_choose 2 h) le_rfl
  | succ hits =>
      cases hits with
      | zero => exact mul_le_mul' (by exact_mod_cast h) le_rfl
      | succ hits => exact le_rfl

private theorem expectation_const_le {Result : Type} (law : SPMF Result) (value : ENNReal) :
    (∑' result, Pr[= result | law] * value) ≤ value := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem pairValue_trial (law : SPMF Bool) (rate : ENNReal) (hrate : law true ≤ rate) (remaining hits : Nat) :
    (∑' hit, Pr[= hit | law] * pairValue rate remaining (hits + if hit then 1 else 0)) ≤
      pairValue rate (remaining + 1) hits := by
  have hfalse : law false ≤ 1 := by
    simpa only [SPMF.probOutput_eq_apply] using (show Pr[= false | law] ≤ 1 from probOutput_le_one)
  cases hits with
  | zero =>
      simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, Nat.zero_add,
        pairValue, SPMF.probOutput_eq_apply]
      calc
        _ ≤ rate * (remaining * rate) + ((remaining.choose 2 : Nat) : ENNReal) * rate ^ 2 :=
          add_le_add (mul_le_mul' hrate le_rfl) (mul_le_of_le_one_left' hfalse)
        _ = _ := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
          ring
  | succ hits =>
      cases hits with
      | zero =>
          simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, Nat.add_zero,
            pairValue, SPMF.probOutput_eq_apply, mul_one]
          calc
            _ ≤ rate + (remaining : ENNReal) * rate := add_le_add hrate (mul_le_of_le_one_left' hfalse)
            _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring
      | succ hits =>
          calc
            _ = ∑' hit, Pr[= hit | law] * 1 := by
              apply tsum_congr
              intro hit
              cases hit <;> rfl
            _ ≤ 1 := expectation_const_le law 1

variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

noncomputable def pairPotential (size budget : Nat) (state : State Coordinate Value Memory) : ENNReal :=
  if state.probes ≤ budget then pairValue ((size - budget : Nat) : ENNReal)⁻¹ (budget - state.probes) state.guesses.card else 0

theorem pairPotential_afterTrial (environment : Environment auxSpec Coordinate Value Memory)
    (size budget : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (coordinate : Coordinate) (candidate : Value) :
    (∑' hit, Pr[= hit | trial state.allowed coordinate candidate] *
      pairPotential size budget (afterTrial environment state coordinate candidate hit)) ≤ pairPotential size budget state := by
  classical
  by_cases hroom : state.probes < budget
  · have hwithin : state.probes ≤ budget := Nat.le_of_lt hroom
    have hafter : state.probes + 1 ≤ budget := hroom
    have hremaining : budget - state.probes = (budget - (state.probes + 1)) + 1 := by omega
    have hp (hit : Bool) : (afterTrial environment state coordinate candidate hit).probes = state.probes + 1 := rfl
    simp only [pairPotential, hp, afterTrial_guesses_card environment state hs.2, if_pos hafter, if_pos hwithin]
    by_cases hc : coordinate ∈ state.retired
    · simp only [hc, not_true_eq_false, and_false, if_false, Nat.add_zero]
      exact (expectation_const_le _ _).trans (pairValue_mono _ _ (Nat.sub_le_sub_left (by omega) _))
    · simp only [hc, not_false_eq_true, and_true]
      rw [hremaining]
      exact pairValue_trial _ _ (trial_true_le size budget state hs ha hwithin coordinate hc candidate) _ _
  · have hafter : ¬state.probes + 1 ≤ budget := by omega
    simp only [pairPotential, afterTrial, if_neg hafter, mul_zero, tsum_zero]
    exact bot_le

theorem lazyImpl_pairPotential (environment : Environment auxSpec Coordinate Value Memory)
    (size budget : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (input : (World auxSpec Coordinate Value).Domain) :
    (∑' result, Pr[= result | (lazyImpl environment input).run state] * pairPotential size budget result.2) ≤
      pairPotential size budget state := by
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, tsum_probOutput_map_mul]
      exact expectation_const_le _ _
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [lazyImpl, StateT.run_mk, tsum_probOutput_map_mul]
          exact pairPotential_afterTrial environment size budget state hs ha coordinate candidate
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, tsum_probOutput_map_mul]
          exact expectation_const_le _ _

theorem lazyRun_pairPotential {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (size budget : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Invariant size state)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) :
    (∑' result, Pr[= result | lazyRun environment computation state] * pairPotential size budget result.2) ≤
      pairPotential size budget state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [lazyRun, runWith_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [lazyRun, runWith_query_bind, tsum_probOutput_bind_mul]
      apply le_trans _ (lazyImpl_pairPotential environment size budget state hs ha input)
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : (lazyImpl environment input).run state middle = 0
      · simp only [SPMF.probOutput_eq_apply, hm, zero_mul, le_refl]
      · have hrun : lazyRun environment (liftM ((World auxSpec Coordinate Value).query input)) state middle ≠ 0 := by
          simpa only [lazyRun, runWith, simulateQ_spec_query] using hm
        exact mul_le_mul' le_rfl (ih middle.1 middle.2
          (lazyRun_invariant environment size _ state hs middle hrun) (lazyRun_nonempty environment _ state ha middle hrun))

omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem pairPotential_two (size budget : Nat) (state : State Coordinate Value Memory)
    (hbudget : state.probes ≤ budget) (hhits : 2 ≤ state.guesses.card) : 1 ≤ pairPotential size budget state := by
  rw [pairPotential, if_pos hbudget]
  obtain ⟨hits, heq⟩ := Nat.exists_eq_add_of_le hhits
  rw [heq, Nat.add_comm]
  exact le_rfl

theorem lazyRun_two_guesses [Fintype Value] [Nonempty Value] {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (hbudget : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → result.2.probes ≤ budget) :
    Pr[fun result => 2 ≤ result.2.guesses.card | lazyRun environment computation (initialState memory)] ≤
      (budget.choose 2 : ENNReal) * ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ ^ 2 := by
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => pairPotential (Fintype.card Value) budget result.2) ?_).trans
      (lazyRun_pairPotential environment (Fintype.card Value) budget computation (initialState memory)
        (initialState_invariant memory) (fun _ => Finset.univ_nonempty))
  intro result hr htwo
  apply pairPotential_two _ _ result.2 _ htwo
  exact hbudget result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr)

end SphincsSecurity.Concrete.SecretGuessObservation
