import FORS.Scheme.Lemmas

/-!
# Exhausting a search

Both of the signer's searches walk a sequence of distinct hash inputs and stop at the first answer
that is accepted: the randomizer search over trial numbers, the counter search over counters. This
file bounds the probability that one such search exhausts every trial.

The argument is the lazy random oracle's defining property. An input the cache has never seen is
answered by a uniform draw, so one trial rejects with exactly the share of answers the acceptance
test rejects, and the answer it caches is at an input no later trial visits. Stepping the induction
therefore preserves the freshness hypothesis and multiplies one rejection factor per trial.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000

namespace FORS.Completeness

variable [Params]

variable {β γ : Type}

/-- A search: query `inputs t`, and stop at the first answer the decoder accepts, running `success` on what it decoded. Both of the signer's searches have this shape. -/
def searchLoop (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ) : Nat → Nat → OracleComp HashSpec (Option γ)
  | 0, _ => pure none
  | n + 1, t => do
      let answer ← Concrete.oracleHash (inputs t)
      match decode answer with
      | some value => some <$> success t value
      | none => searchLoop inputs decode success n (t + 1)

/-- The share of answers one trial rejects. -/
noncomputable def failMass (decode : HashOutput → Option β) : ℝ≥0∞ :=
  ((Finset.univ.filter fun u => decode u = none).card : ℝ≥0∞) / (Fintype.card HashOutput : ℝ≥0∞)

/-- The rejection share is the probability that one uniform answer is rejected. -/
theorem failMass_eq_probEvent (decode : HashOutput → Option β) :
    failMass decode = Pr[fun u => decode u = none | ($ᵗ HashOutput : ProbComp HashOutput)] :=
  (probEvent_uniformSample HashOutput _).symm

/-- A query on an uncached input samples its answer uniformly. -/
theorem fresh_run (input : HashInput) (cache : QueryCache HashSpec) (hfresh : cache input = none)
    {δ : Type} (next : HashOutput × QueryCache HashSpec → ProbComp δ) (p : δ → Prop) :
    Pr[p | (randomOracle (spec := HashSpec) input).run cache >>= next]
      = ∑' u : HashOutput, (Fintype.card HashOutput : ℝ≥0∞)⁻¹
          * Pr[p | next (u, cache.cacheQuery input u)] := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_def, pure_bind]
  rw [show (uniformSampleImpl (spec := HashSpec) input) = ($ᵗ HashOutput : ProbComp HashOutput)
    from rfl, probEvent_bind_eq_tsum]
  exact tsum_congr fun u => by rw [probOutput_uniformSample]

/-- A search over fresh inputs, distinct below `bound`, exhausts all `n` trials with probability at most the per-trial rejection share to the `n`. The bound is what the counter search needs: its inputs carry a 32-bit counter, so they repeat only after `2 ^ 32` trials, which is exactly its trial budget. -/
theorem probEvent_searchLoop (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ) (bound : Nat)
    (hinj : ∀ s s', s < bound → s' < bound → inputs s = inputs s' → s = s') :
    ∀ (n t : Nat), t + n ≤ bound → ∀ cache : QueryCache HashSpec,
      (∀ s, t ≤ s → s < bound → cache (inputs s) = none) →
      Pr[fun r => r.1 = none |
          (simulateQ randomOracle (searchLoop inputs decode success n t)).run cache]
        ≤ failMass decode ^ n := by
  intro n
  induction n with
  | zero => intro t _ cache _; simp [searchLoop]
  | succ n ih =>
      intro t hbound cache hfresh
      rw [searchLoop]
      simp only [Concrete.oracleHash, HasQuery.query, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind]
      rw [fresh_run (inputs t) cache (hfresh t (Nat.le_refl t) (by omega))]
      have hterm : ∀ u : HashOutput,
          Pr[fun r => r.1 = none | (simulateQ randomOracle
              (match decode u with
                | some value => some <$> success t value
                | none => searchLoop inputs decode success n (t + 1))).run
              (cache.cacheQuery (inputs t) u)]
            ≤ (if decode u = none then failMass decode ^ n else 0) := by
        intro u
        cases hu : decode u with
        | some value =>
            simp only [reduceCtorEq, if_false, simulateQ_map, StateT.run_map, probEvent_map]
            simp
        | none =>
            simp only [if_true]
            refine ih (t + 1) (by omega) _ (fun s hs hsb => ?_)
            have hne : inputs s ≠ inputs t := fun hcon => by
              have hst := hinj s t hsb (by omega) hcon
              omega
            exact (QueryCache.cacheQuery_of_ne cache u hne).trans
              (hfresh s (Nat.le_of_succ_le hs) hsb)
      refine le_trans (ENNReal.tsum_le_tsum (fun u => mul_le_mul_right (hterm u) _)) ?_
      rw [tsum_fintype, Finset.sum_congr rfl (fun u _ => by rw [mul_ite, mul_zero]),
        Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        pow_succ', failMass, div_eq_mul_inv, ← mul_assoc]

end FORS.Completeness
