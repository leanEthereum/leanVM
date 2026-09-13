import XmssSecurity.Proof.Seeded.HashTrace

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

open scoped Classical in
theorem probOutput_stopBefore_seed_le {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat) (hbound : HashQueryBound computation cache q) :
    Pr[= none | sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (stopBefore (hashBad (fun input => SeedHit input seed)) computation)).run' cache] ≤
        q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let trace := (simulateQ romImpl (traceHashes computation)).run' cache
  calc
    _ = Pr[= true | sampleMasterSeed >>= fun seed =>
        (fun result => decide (SeedHitLog result.2 seed)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, probOutput_stopBefore_none, probOutput_map,
        decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun seed => decide (SeedHitLog result.2 seed)) <$> sampleMasterSeed] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_of_forall_le
      intro result hresult
      simp only [probEvent_map, Function.comp_def, decide_eq_true_eq]
      exact (probEvent_seedHitLog_le result.2).trans
        (ENNReal.div_le_div
          (by exact_mod_cast traceHashes_length_le computation cache q hbound result hresult) le_rfl)

open scoped Classical in
theorem probEvent_random_cache_change_le {α : Type} (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (fun input => SeedHit input seed) (initial seed) cache)
    (q : Nat) (hbound : HashQueryBound computation cache q) (event : α → Prop) :
    Pr[event | sampleMasterSeed >>= fun seed => (simulateQ romImpl computation).run' (initial seed)] ≤
      Pr[event | (simulateQ romImpl computation).run' cache] + q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let stopped := fun seed =>
    (simulateQ romImpl (stopBefore (hashBad (fun input => SeedHit input seed)) computation)).run' cache
  calc
    _ ≤ Pr[event | sampleMasterSeed >>= fun _ => (simulateQ romImpl computation).run' cache] +
        Pr[= none | sampleMasterSeed >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun seed =>
        (mul_le_mul' le_rfl (probEvent_cache_change_le (fun input => SeedHit input seed)
          computation (initial seed) cache (hagree seed) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add (le_refl (Pr[event | (simulateQ romImpl computation).run' cache]))
        (probOutput_stopBefore_seed_le computation cache q hbound)

end XmssSecurity.Seeded
