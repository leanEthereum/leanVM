import SphincsSecurity.Proof.Chains.PartialChainTwoEdgeCharge
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]

noncomputable def twoEdgeWeight {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) : ENNReal :=
  meanPreimages observed endpoint * if TwoEdge observed endpoint then 1 else 0

theorem twoEdgeWeight_empty {n : Nat} (endpoint : State) :
    twoEdgeWeight (n := n) (fun _ _ => none) endpoint = 0 := by
  simp [twoEdgeWeight, TwoEdge]

omit [DecidableEq State] [Nonempty State] in
private theorem expected_charge_cover (law : PMF State) (before increment : Nat) (after : State → Nat)
    (weight : State → ENNReal)
    (hrisk : (∑' answer, law answer * weight answer) ≤ (increment : ENNReal) / Fintype.card State)
    (hcharge : ∀ answer, before + increment ≤ after answer) :
    (before : ENNReal) / Fintype.card State + (∑' answer, law answer * weight answer) ≤
      ∑' answer, law answer * ((after answer : ENNReal) / Fintype.card State) := by
  calc
    _ ≤ (before : ENNReal) / Fintype.card State + (increment : ENNReal) / Fintype.card State := _root_.add_le_add le_rfl hrisk
    _ = ((before + increment : Nat) : ENNReal) / Fintype.card State := by simp only [Nat.cast_add, div_eq_mul_inv, add_mul]
    _ = ∑' answer, law answer * (((before + increment : Nat) : ENNReal) / Fintype.card State) := (expectation_const _ _).symm
    _ ≤ _ := ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (by gcongr; exact_mod_cast hcharge answer)

theorem twoEdgeCharge_observe_mono {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State ≤
      ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  cases hrow : observed query.1 query.2 with
  | some answer =>
      simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
      gcongr
      exact twoEdgeCharge_mono (Nat.le_succ spent) (fun _ _ _ h => h) endpoint
  | none =>
      rw [← expectation_const (rowLaw (none : Option State)) ((twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State)]
      apply ENNReal.tsum_le_tsum
      intro answer
      apply mul_le_mul' le_rfl
      gcongr
      exact twoEdgeCharge_mono (Nat.le_succ spent) (record_extends observed query answer (Or.inl hrow)) endpoint

theorem twoEdgeWeight_observe_of_bad {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) (hbad : TwoEdge observed endpoint) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) =
      twoEdgeWeight observed endpoint := by
  cases hrow : observed query.1 query.2 with
  | some answer => simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
  | none =>
      have hafter (answer : State) : TwoEdge (record observed query answer) endpoint :=
        twoEdge_mono (record_extends observed query answer (Or.inl hrow)) endpoint hbad
      simp only [twoEdgeWeight, if_pos hbad, if_pos (hafter _), mul_one]
      simpa only [hrow] using meanPreimages_observe observed query endpoint

theorem twoEdge_first_compensation {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) (hbad : ¬TwoEdge observed endpoint)
    (hfresh : observed query.1 query.2 = none) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) ≤
      ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  rcases query with ⟨step, input⟩
  by_cases hlast : step = Fin.last (n + 1)
  · subst step
    by_cases hprepared : ∃ start, observed (Fin.last n).castSucc start = some input
    · apply expected_charge_cover _ _ (2 + contactCount observed endpoint + targetCount (Fin.init observed) input)
      · simpa only [twoEdgeWeight, if_pos hprepared] using twoEdge_last_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        exact twoEdgeCharge_record_last spent observed input answer endpoint hfresh hprepared
    · apply expected_charge_cover _ _ 0
      · simpa only [twoEdgeWeight, if_neg hprepared, Nat.cast_zero, div_eq_mul_inv, zero_mul] using twoEdge_last_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        simpa only [Nat.add_zero] using twoEdgeCharge_mono (Nat.le_succ spent)
          (record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh)) endpoint
  · by_cases hpen : step = (Fin.last n).castSucc
    · subst step
      apply expected_charge_cover _ _ (contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input))
      · exact twoEdge_penultimate_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        exact twoEdgeCharge_record_penultimate spent observed input answer endpoint hfresh
    · have hafter (answer : State) : ¬TwoEdge (record observed (step, input) answer) endpoint := by
        rw [twoEdge_record_earlier observed (step, input) answer endpoint (Ne.symm hpen) (Ne.symm hlast)]
        exact hbad
      simp only [twoEdgeWeight, if_neg (hafter _), mul_zero, tsum_zero, add_zero]
      exact twoEdgeCharge_observe_mono spent observed (step, input) endpoint

theorem twoEdge_observe_compensation {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) ≤
      twoEdgeWeight observed endpoint + ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  by_cases hbad : TwoEdge observed endpoint
  · rw [twoEdgeWeight_observe_of_bad observed query endpoint hbad, add_comm]
    exact _root_.add_le_add le_rfl (twoEdgeCharge_observe_mono spent observed query endpoint)
  · have hzero : twoEdgeWeight observed endpoint = 0 := by simp only [twoEdgeWeight, if_neg hbad, mul_zero]
    rw [hzero, zero_add]
    cases hrow : observed query.1 query.2 with
    | none => simpa only [hrow] using twoEdge_first_compensation spent observed query endpoint hbad hrow
    | some answer =>
        simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow, hzero, add_zero]
        gcongr
        exact twoEdgeCharge_mono (Nat.le_succ spent) (fun _ _ _ h => h) endpoint

end SphincsSecurity.Concrete.PartialChainEndpoint
