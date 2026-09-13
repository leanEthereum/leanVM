import SphincsSecurity.Proof.Forced.SecretGuessHitRun
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem sum_bind_apply {Index First Result : Type} (indices : Finset Index) (law : SPMF First)
    (next : Index → First → SPMF Result) (result : Result) :
    (∑ index ∈ indices, (law >>= next index) result) =
      ∑' first, law first * ∑ index ∈ indices, next index first result := by
  simp only [SPMF.bind_apply_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [Finset.mul_sum]

variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

theorem hitImpl_no_probe (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0) :
    hitImpl environment slot input = lazyImpl environment input := by
  cases input with
  | inl input => rfl
  | inr input =>
      cases input with
      | inl probe => cases hn
      | inr coordinate => rfl

theorem lazyImpl_no_probe_guesses (environment : Environment auxSpec Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0)
    (state : State Coordinate Value Memory) (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (lazyImpl environment input).run state result ≠ 0) : result.2.guesses = state.guesses := by
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      rfl
  | inr input =>
      cases input with
      | inl probe => cases hn
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨value, _, rfl⟩ := hr
          rfl

theorem hitRun_sum_no_probe {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (slots : Finset Nat) (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory) :
    (∑ slot ∈ slots, hitRun environment slot (liftM ((World auxSpec Coordinate Value).query input) >>= next) state result) =
      ∑' middle, (lazyImpl environment input).run state middle *
        ∑ slot ∈ slots, hitRun environment slot (next middle.1) middle.2 result := by
  simp_rw [hitRun_query_bind, hitImpl_no_probe environment _ input hn]
  exact sum_bind_apply slots _ _ result

theorem hitRun_sum_probe {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (budget : Nat)
    (coordinate : Coordinate) (candidate : Value) (next : Bool → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory) (hbudget : state.probes < budget) :
    (∑ slot ∈ Finset.Ico state.probes budget, hitRun environment slot
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result) =
      ∑' hit, trial state.allowed coordinate candidate hit *
        ((if hit = true ∧ coordinate ∉ state.retired then lazyRun environment (next hit) (afterTrial environment state coordinate candidate hit) result else 0) +
          ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
            hitRun environment slot (next hit) (afterTrial environment state coordinate candidate hit) result) := by
  rw [Finset.sum_eq_sum_Ico_succ_bot hbudget, hitRun_probe_at, SPMF.bind_apply_eq_tsum]
  have htail :
      (∑ slot ∈ Finset.Ico (state.probes + 1) budget, hitRun environment slot
        (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result) =
      ∑' hit, trial state.allowed coordinate candidate hit *
        ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
          hitRun environment slot (next hit) (afterTrial environment state coordinate candidate hit) result := by
    calc
      _ = ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
          (trial state.allowed coordinate candidate >>= fun hit =>
            hitRun environment slot (next hit) (afterTrial environment state coordinate candidate hit)) result := by
        apply Finset.sum_congr rfl
        intro slot hslot
        rw [hitRun_probe_other environment slot coordinate candidate next state (by
          have h := (Finset.mem_Ico.mp hslot).1
          omega)]
      _ = _ := sum_bind_apply _ _ _ result
  rw [htail, ← ENNReal.tsum_add]
  apply tsum_congr
  intro hit
  by_cases hh : hit = true ∧ coordinate ∉ state.retired
  · simp only [if_pos hh, mul_add]
  · simp only [if_neg hh, SPMF.failure_apply, mul_zero, zero_add]

theorem lazyRun_new_guesses_le_sum {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) (budget : Nat) (hbudget : result.2.probes ≤ budget)
    (hnew : result.2.guesses ≠ state.guesses) :
    lazyRun environment computation state result ≤
      ∑ slot ∈ Finset.Ico state.probes budget, hitRun environment slot computation state result := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      by_cases he : result = (value, state)
      · subst result
        exact False.elim (hnew rfl)
      · simp only [lazyRun, runWith_pure, SPMF.pure_apply, if_neg he]
        exact bot_le
  | query_bind input next ih =>
      by_cases hn : probeStep input = 0
      · rw [hitRun_sum_no_probe environment _ input hn, lazyRun, runWith_query_bind, SPMF.bind_apply_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro middle
        by_cases hm : (lazyImpl environment input).run state middle = 0
        · simp only [hm, zero_mul, le_refl]
        · have hp := lazyImpl_probes environment state input middle hm
          rw [hn, Nat.add_zero] at hp
          have hg := lazyImpl_no_probe_guesses environment input hn state middle hm
          have h := ih middle.1 middle.2 (hg ▸ hnew)
          rw [hp] at h
          exact mul_le_mul' le_rfl h
      · cases input with
        | inl input => exact False.elim (hn rfl)
        | inr input =>
            cases input with
            | inr coordinate => exact False.elim (hn rfl)
            | inl probe =>
                rcases probe with ⟨coordinate, candidate⟩
                by_cases hz : lazyRun environment
                    (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result = 0
                · rw [hz]
                  exact bot_le
                have hpositive := hz
                rw [lazyRun, runWith_query_bind] at hpositive
                simp only [lazyImpl, StateT.run_mk, bind_map_left, RetainedObservation.bind_nonzero] at hpositive
                obtain ⟨hit, _, htail⟩ := hpositive
                have hp := lazyRun_probes_mono environment (next hit) (afterTrial environment state coordinate candidate hit) result htail
                have hroom : state.probes < budget := by
                  change state.probes + 1 ≤ result.2.probes at hp
                  omega
                rw [hitRun_sum_probe environment budget coordinate candidate next state result hroom]
                simp only [lazyRun, runWith_query_bind, lazyImpl, StateT.run_mk, bind_map_left, SPMF.bind_apply_eq_tsum]
                apply ENNReal.tsum_le_tsum
                intro hit
                apply mul_le_mul' le_rfl
                by_cases hh : hit = true ∧ coordinate ∉ state.retired
                · rw [if_pos hh]
                  exact le_add_right le_rfl
                · rw [if_neg hh, zero_add]
                  apply ih hit (afterTrial environment state coordinate candidate hit)
                  simpa only [afterTrial, if_neg hh] using hnew

end SphincsSecurity.Concrete.SecretGuessObservation
