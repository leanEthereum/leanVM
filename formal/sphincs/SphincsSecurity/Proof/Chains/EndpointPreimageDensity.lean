import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity.Concrete.EndpointPreimageDensity

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Table State : Type} [Fintype State] [Nonempty State] [DecidableEq State] [DecidableEq Table]

noncomputable def preimages (evaluate : Table → State → State) (table : Table) (endpoint : State) : Nat :=
  (Finset.univ.filter (fun secret => evaluate table secret = endpoint)).card

noncomputable def real (prior : PMF Table) (evaluate : Table → State → State) : PMF (Table × State) :=
  prior.bind (fun table => ((PMF.uniformOfFintype State).map (evaluate table)).map (fun endpoint => (table, endpoint)))

noncomputable def ideal (prior : PMF Table) : PMF (Table × State) :=
  prior.bind (fun table => (PMF.uniformOfFintype State).map (fun endpoint => (table, endpoint)))

theorem uniform_image_apply (evaluate : State → State) (endpoint : State) :
    (PMF.uniformOfFintype State).map evaluate endpoint =
      ((Finset.univ.filter (fun secret => evaluate secret = endpoint)).card : ENNReal) / Fintype.card State := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, eq_comm, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

omit [Fintype State] [Nonempty State] [DecidableEq State] in
theorem map_pair_apply (law : PMF State) (table target : Table) (endpoint : State) :
    law.map (fun value => (table, value)) (target, endpoint) = if table = target then law endpoint else 0 := by
  rw [PMF.map_apply]
  by_cases htable : table = target
  · subst target
    rw [if_pos rfl, tsum_eq_single endpoint]
    · rw [if_pos rfl]
    · intro value hvalue
      exact if_neg (fun h => hvalue (congrArg Prod.snd h).symm)
  · rw [if_neg htable]
    apply ENNReal.tsum_eq_zero.mpr
    intro value
    exact if_neg (fun h => htable (congrArg Prod.fst h).symm)

omit [Fintype State] [Nonempty State] [DecidableEq State] in
theorem bind_pair_apply (prior : PMF Table) (law : Table → PMF State) (table : Table) (endpoint : State) :
    prior.bind (fun selected => (law selected).map (fun value => (selected, value))) (table, endpoint) =
      prior table * law table endpoint := by
  rw [PMF.bind_apply]
  simp only [map_pair_apply, mul_ite, mul_zero]
  rw [tsum_eq_single table]
  · simp only [if_true]
  · intro selected hselected
    exact if_neg hselected

theorem real_apply (prior : PMF Table) (evaluate : Table → State → State) (table : Table) (endpoint : State) :
    real prior evaluate (table, endpoint) = prior table * ((preimages evaluate table endpoint : ENNReal) / Fintype.card State) := by
  rw [real, bind_pair_apply, uniform_image_apply]
  rfl

omit [DecidableEq State] in
theorem ideal_apply (prior : PMF Table) (table : Table) (endpoint : State) :
    ideal prior (table, endpoint) = prior table / Fintype.card State := by
  rw [ideal, bind_pair_apply, PMF.uniformOfFintype_apply, div_eq_mul_inv]

theorem real_density (prior : PMF Table) (evaluate : Table → State → State) (table : Table) (endpoint : State) :
    real prior evaluate (table, endpoint) = (preimages evaluate table endpoint : ENNReal) * ideal prior (table, endpoint) := by
  rw [real_apply, ideal_apply]
  simp only [div_eq_mul_inv]
  ring

theorem real_payoff (prior : PMF Table) (evaluate : Table → State → State) (payoff : Table × State → ENNReal) :
    (∑' result, real prior evaluate result * payoff result) =
      ∑' result : Table × State, ideal prior result * (preimages evaluate result.1 result.2 : ENNReal) * payoff result := by
  apply tsum_congr
  rintro ⟨table, endpoint⟩
  rw [real_density]
  ring

omit [DecidableEq Table] in
theorem mean_preimages (prior : PMF Table) (evaluate : Table → State → State) (endpoint : State) :
    (∑' table, prior table * (preimages evaluate table endpoint : ENNReal)) =
      (Fintype.card State : ENNReal) *
        prior.bind (fun table => (PMF.uniformOfFintype State).map (evaluate table)) endpoint := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro table
  rw [uniform_image_apply]
  change prior table * (preimages evaluate table endpoint : ENNReal) =
    (Fintype.card State : ENNReal) * (prior table * ((preimages evaluate table endpoint : ENNReal) / Fintype.card State))
  rw [div_eq_mul_inv]
  calc
    _ = ((Fintype.card State : ENNReal) * (Fintype.card State : ENNReal)⁻¹) *
        (prior table * (preimages evaluate table endpoint : ENNReal)) := by
      rw [ENNReal.mul_inv_cancel hcard (by finiteness), one_mul]
    _ = _ := by ring

end SphincsSecurity.Concrete.EndpointPreimageDensity
