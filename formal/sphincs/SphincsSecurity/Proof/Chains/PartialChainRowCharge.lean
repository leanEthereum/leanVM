import SphincsSecurity.Proof.Chains.PartialChainTwoEdge
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem weighted_event_le_bound {Result : Type} (law : PMF Result) (weight : Result → ENNReal)
    (event : Result → Prop) [DecidablePred event] (bound : ENNReal) (hbound : ∀ result, weight result ≤ bound) :
    (∑' result, law result * (weight result * if event result then 1 else 0)) ≤ bound * Pr[event | law] := by
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hevent : event result
  · simpa only [hevent, if_true, mul_one, PMF.probOutput_eq_apply, mul_comm] using mul_le_mul' (hbound result) (le_refl (law result))
  · simp only [hevent, if_false, mul_zero, le_refl]

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]

omit [DecidableEq State] in
theorem kernel_snoc {n : Nat} (before : Fin n → State → Option State) (last : State → Option State) :
    kernel (Fin.snoc before last) = fun start => (kernel before start).bind (fun input => rowLaw (last input)) := by
  induction n with
  | zero => funext start; simp [kernel, Fin.snoc_zero]
  | succ n ih =>
      funext start
      have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
      rw [hs, kernel, Fin.cons_zero, Fin.tail_cons]
      rw [ih]
      simp only [kernel, PMF.bind_bind]

theorem row_update_charge (prior : PMF State) (observed : State → Option State) (next : State → PMF State)
    (input answer endpoint : State) :
    prior.bind (fun start => (rowLaw (Function.update observed input (some answer) start)).bind next) endpoint ≤
      prior.bind (fun start => (rowLaw (observed start)).bind next) endpoint + prior input := by
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' start, prior start * (((rowLaw (observed start)).bind next) endpoint + if start = input then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro start
      apply mul_le_mul' le_rfl
      by_cases hs : start = input
      · rw [if_pos hs]
        exact (PMF.coe_le_one _ endpoint).trans (_root_.le_add_of_nonneg_left bot_le)
      · simp only [Function.update_of_ne hs, if_neg hs, add_zero, le_refl]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, tsum_ite_eq, PMF.bind_apply]

theorem meanPreimages_last_update_le {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer endpoint : State) :
    meanPreimages (Fin.snoc before (Function.update last input (some answer))) endpoint ≤
      meanPreimages (Fin.snoc before last) endpoint + meanPreimages before input := by
  have h := row_update_charge ((PMF.uniformOfFintype State).bind (kernel before)) last PMF.pure input answer endpoint
  simp only [PMF.bind_pure] at h
  have hscaled := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) h
  simpa only [meanPreimages_eq, kernel_snoc, PMF.bind_bind, mul_add] using hscaled

theorem meanPreimages_penultimate_update_le {n : Nat} (before : Fin n → State → Option State)
    (penultimate last : State → Option State) (input answer endpoint : State) :
    meanPreimages (Fin.snoc (Fin.snoc before (Function.update penultimate input (some answer))) last) endpoint ≤
      meanPreimages (Fin.snoc (Fin.snoc before penultimate) last) endpoint + meanPreimages before input := by
  have h := row_update_charge ((PMF.uniformOfFintype State).bind (kernel before)) penultimate
    (fun middle => rowLaw (last middle)) input answer endpoint
  have hscaled := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) h
  simpa only [meanPreimages_eq, kernel_snoc, PMF.bind_bind, mul_add] using hscaled

theorem meanPreimages_record_last_le {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (input answer endpoint : State) :
    meanPreimages (record observed (Fin.last n, input) answer) endpoint ≤
      meanPreimages observed endpoint + meanPreimages (Fin.init observed) input := by
  have h := meanPreimages_last_update_le (Fin.init observed) (observed (Fin.last n)) input answer endpoint
  rw [Fin.snoc_init_self] at h
  have hrecord : record observed (Fin.last n, input) answer =
      Fin.snoc (Fin.init observed) (Function.update (observed (Fin.last n)) input (some answer)) := by
    conv_lhs => rw [← Fin.snoc_init_self observed]
    simp only [record, Fin.snoc_last, Fin.update_snoc_last]
  simpa only [hrecord] using h

theorem meanPreimages_record_penultimate_le {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) :
    meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint ≤
      meanPreimages observed endpoint + meanPreimages (Fin.init (Fin.init observed)) input := by
  have h := meanPreimages_penultimate_update_le (Fin.init (Fin.init observed)) ((Fin.init observed) (Fin.last n))
    (observed (Fin.last (n + 1))) input answer endpoint
  rw [Fin.snoc_init_self, Fin.snoc_init_self] at h
  have hrecord : record observed ((Fin.last n).castSucc, input) answer =
      Fin.snoc (Fin.snoc (Fin.init (Fin.init observed))
        (Function.update ((Fin.init observed) (Fin.last n)) input (some answer))) (observed (Fin.last (n + 1))) := by
    conv_lhs => rw [← Fin.snoc_init_self observed, ← Fin.snoc_init_self (Fin.init observed)]
    simp only [record, Fin.snoc_castSucc, Fin.snoc_last, ← Fin.snoc_update, Fin.update_snoc_last]
  simpa only [hrecord] using h

theorem twoEdge_last_density_charge {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint ≤
      (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat) := by
  have hprefix := meanPreimages_le_suffixCount (Fin.init observed) input
  rw [suffixCount_eq_targetCount] at hprefix
  apply (meanPreimages_record_last_le observed input answer endpoint).trans
  have hsum := _root_.add_le_add (meanPreimages_le_contactCount_of_no_twoEdge observed endpoint h) hprefix
  convert hsum using 1
  push_cast
  ring

theorem twoEdge_penultimate_density_charge {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint ≤
      (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input : Nat) := by
  have hprefix := meanPreimages_le_suffixCount (Fin.init (Fin.init observed)) input
  rw [suffixCount_eq_targetCount] at hprefix
  apply (meanPreimages_record_penultimate_le observed input answer endpoint).trans
  have hsum := _root_.add_le_add (meanPreimages_le_contactCount_of_no_twoEdge observed endpoint h) hprefix
  convert hsum using 1
  push_cast
  ring

theorem twoEdge_last_weighted_risk {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input endpoint : State) (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last (n + 1)) input = none) :
    (∑' answer, rowLaw (observed (Fin.last (n + 1)) input) answer *
      (meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint *
        if TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint then 1 else 0)) ≤
      if ∃ start, observed (Fin.last n).castSucc start = some input then
        (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat) / (Fintype.card State : ENNReal) else 0 := by
  classical
  apply (weighted_event_le_bound (rowLaw (observed (Fin.last (n + 1)) input))
    (fun answer => meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint)
    (fun answer => TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint)
    (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat)
    (fun answer => twoEdge_last_density_charge observed input answer endpoint h)).trans_eq
  rw [twoEdge_last_probability observed input endpoint h hfresh]
  split <;> simp only [mul_zero, div_eq_mul_inv, one_mul]

theorem twoEdge_penultimate_weighted_risk {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input endpoint : State) (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last n).castSucc input = none) :
    (∑' answer, rowLaw (observed (Fin.last n).castSucc input) answer *
      (meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint *
        if TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint then 1 else 0)) ≤
      (contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input) : Nat) /
        (Fintype.card State : ENNReal) := by
  classical
  apply (weighted_event_le_bound (rowLaw (observed (Fin.last n).castSucc input))
    (fun answer => meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint)
    (fun answer => TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint)
    (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input : Nat)
    (fun answer => twoEdge_penultimate_density_charge observed input answer endpoint h)).trans_eq
  rw [twoEdge_penultimate_probability observed input endpoint h hfresh]
  simp only [Nat.cast_mul, div_eq_mul_inv]
  ring

end SphincsSecurity.Concrete.PartialChainEndpoint
