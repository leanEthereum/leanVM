import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CachedDigestSelection
import SphincsSecurity.Proof.Fts.FewTimeFreshMass
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop

private theorem digestSelection_partition (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result)
    (hr : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run cache)) :
    (if freshSelectedLoopView? cache key message result ≠ none then (1 : ENNReal) else 0) +
      (if PrehitSelectedView cache key message (fun _ => True) result then 1 else 0) +
      (if result.1 = none then 1 else 0) = 1 := by
  obtain ⟨selected, after⟩ := result
  cases selected with
  | none => simp [freshSelectedLoopView?, PrehitSelectedView]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      cases hc : cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) with
      | none => simp [freshSelectedLoopView?, PrehitSelectedView, hc]
      | some output =>
          have hp : PrehitSelectedView cache key message (fun _ => True) (some (randomness, index, leaves), after) :=
            ⟨randomness, index, leaves, rfl, output, hc,
              signDigestLoop_initial_cached_result attempts key message randomness index leaves cache after output hc hr, trivial⟩
          simp only [freshSelectedLoopView?, hc, Option.some_ne_none, if_false, ne_eq, not_true_eq_false, hp,
            if_true, zero_add, add_zero]

theorem probEvent_signDigestLoop_selection_mass (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    Pr[fun result => freshSelectedLoopView? cache key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] +
      Pr[PrehitSelectedView cache key message (fun _ => True) |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] +
      Pr[fun result => result.1 = none | (simulateQ romImpl (signDigestLoop attempts key message)).run cache] = 1 := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ = ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop attempts key message)).run cache] := by
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run cache)
      · have h := congrArg (fun value => Pr[= result | (simulateQ romImpl (signDigestLoop attempts key message)).run cache] * value)
          (digestSelection_partition attempts key message cache result hr)
        simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
      · simp only [probOutput_eq_zero_of_not_mem_support hr, ite_self, zero_add]
    _ = 1 := tsum_probOutput_of_liftM_PMF _

noncomputable def digestExhaustionProbability (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun result => result.1 = none | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache]

theorem freshSelection_add_cachedAttempts_add_exhaustion (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache +
      cachedDigestAttemptRate key message cache (fun _ => True) * digestAttemptExpectation digestAttemptLimit key message cache +
      digestExhaustionProbability key message cache = 1 := by
  have h := probEvent_signDigestLoop_selection_mass digestAttemptLimit key message cache
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message cache cache le_rfl] at h
  exact h

end SphincsSecurity.Concrete
