import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Chains.EndpointPreimageDensity
import SphincsSecurity.Proof.Base.FinitePmfProductObservation
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]

noncomputable def rowLaw : Option State → PMF State
  | none => PMF.uniformOfFintype State
  | some value => PMF.pure value

noncomputable def completeFunction (observed : State → Option State) : PMF (State → State) :=
  FinitePmfProduct.law (fun input => rowLaw (observed input))

theorem completeFunction_marginal (observed : State → Option State) (input : State) :
    (completeFunction observed).map (fun table => table input) = rowLaw (observed input) :=
  FinitePmfProduct.marginal _ input

def evaluate : {n : Nat} → (Fin n → State → State) → State → State
  | 0, _, start => start
  | _ + 1, tables, start => evaluate (Fin.tail tables) (tables 0 start)

noncomputable def completeTables {n : Nat} (observed : Fin n → State → Option State) :
    PMF (Fin n → State → State) := FinitePmfProduct.law (fun step => completeFunction (observed step))

noncomputable def kernel : {n : Nat} → (Fin n → State → Option State) → State → PMF State
  | 0, _, start => PMF.pure start
  | _ + 1, observed, start => (rowLaw (observed 0 start)).bind (kernel (Fin.tail observed))

theorem completeTables_evaluate {n : Nat} (observed : Fin n → State → Option State) (start : State) :
    (completeTables observed).map (fun tables => evaluate tables start) = kernel observed start := by
  induction n generalizing start with
  | zero => exact PMF.map_const _ _
  | succ n ih =>
      rw [completeTables, FinitePmfProduct.fin_succ, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def, evaluate, Fin.tail_cons, Fin.cons_zero]
      change (completeFunction (observed 0)).bind (fun first =>
        (completeTables (Fin.tail observed)).map (fun tables => evaluate tables (first start))) = _
      simp_rw [ih]
      calc
        _ = ((completeFunction (observed 0)).map (fun first => first start)).bind (kernel (Fin.tail observed)) :=
          (PMF.bind_map _ _ _).symm
        _ = _ := by rw [completeFunction_marginal, kernel]

theorem uniform_endpoint {n : Nat} (observed : Fin n → State → Option State) :
    (completeTables observed).bind (fun tables => (PMF.uniformOfFintype State).map (evaluate tables)) =
      (PMF.uniformOfFintype State).bind (kernel observed) := by
  change (completeTables observed).bind (fun tables =>
    (PMF.uniformOfFintype State).bind (fun start => PMF.pure (evaluate tables start))) = _
  rw [PMF.bind_comm]
  change (PMF.uniformOfFintype State).bind
    (fun start => (completeTables observed).map (fun tables => evaluate tables start)) = _
  simp only [completeTables_evaluate]

noncomputable def meanPreimages {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  ∑' tables, completeTables observed tables * (EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal)

theorem meanPreimages_eq {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    meanPreimages observed endpoint =
      (Fintype.card State : ENNReal) * ((PMF.uniformOfFintype State).bind (kernel observed)) endpoint := by
  rw [meanPreimages, EndpointPreimageDensity.mean_preimages, uniform_endpoint]

noncomputable def unqueried (observed : State → Option State) : Finset State :=
  Finset.univ.filter (fun input => observed input = none)

noncomputable def freeFraction (observed : State → Option State) : ENNReal :=
  (unqueried observed).card / (Fintype.card State : ENNReal)

omit [DecidableEq State] in
theorem advance_lower (observed : State → Option State) (prior : PMF State) (bound : ENNReal)
    (hlower : ∀ input, bound ≤ prior input) (endpoint : State) :
    bound * freeFraction observed ≤ prior.bind (fun input => rowLaw (observed input)) endpoint := by
  rw [PMF.bind_apply, tsum_fintype]
  calc
    _ = ∑ input ∈ unqueried observed, bound * (Fintype.card State : ENNReal)⁻¹ := by
      simp only [Finset.sum_const, nsmul_eq_mul, freeFraction, div_eq_mul_inv]
      ring
    _ ≤ ∑ input ∈ unqueried observed, prior input * rowLaw (observed input) endpoint := by
      apply Finset.sum_le_sum
      intro input hinput
      have hnone : observed input = none := (Finset.mem_filter.mp hinput).2
      rw [hnone, rowLaw, PMF.uniformOfFintype_apply]
      exact mul_le_mul_left (hlower input) _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => bot_le)

omit [DecidableEq State] in
theorem kernel_lower {n : Nat} (observed : Fin n → State → Option State) (prior : PMF State) (bound : ENNReal)
    (hlower : ∀ input, bound ≤ prior input) (endpoint : State) :
    bound * (∏ step, freeFraction (observed step)) ≤ prior.bind (kernel observed) endpoint := by
  induction n generalizing prior bound with
  | zero => simpa only [Fin.prod_univ_zero, mul_one, kernel, PMF.bind_pure] using hlower endpoint
  | succ n ih =>
      rw [Fin.prod_univ_succ, ← mul_assoc]
      have h := ih (Fin.tail observed) (prior.bind (fun input => rowLaw (observed 0 input)))
        (bound * freeFraction (observed 0)) (advance_lower (observed 0) prior bound hlower)
      simpa only [PMF.bind_bind, kernel, Fin.tail] using h

theorem meanPreimages_ge_product {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    (∏ step, freeFraction (observed step)) ≤ meanPreimages observed endpoint := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [meanPreimages_eq]
  have h := mul_le_mul_right (kernel_lower observed (PMF.uniformOfFintype State) (Fintype.card State : ENNReal)⁻¹
    (fun input => by rw [PMF.uniformOfFintype_apply]) endpoint) (Fintype.card State : ENNReal)
  simpa only [← mul_assoc, ENNReal.mul_inv_cancel hcard (by finiteness), one_mul] using h

end SphincsSecurity.Concrete.PartialChainEndpoint
