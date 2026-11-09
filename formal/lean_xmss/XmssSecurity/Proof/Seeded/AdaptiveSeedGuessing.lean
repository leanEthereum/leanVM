module

public import XmssSecurity.Proof.Seeded.HashTrace
public import XmssSecurity.Proof.Seeded.SeedGuessing

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

open scoped Classical in
theorem probOutput_stopBefore_seed_le {hit : HashInput → MasterSeed → Prop} (hhit : GuessBound hit)
    {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat) (hbound : HashQueryBound computation cache q) :
    Pr{let x ← (sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (stopBefore (hashBad (fun input => hit input seed)) computation)).run' cache)}[x = none] ≤
        q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let trace := (simulateQ romImpl (traceHashes computation)).run' cache
  calc
    _ = Pr{let x ← (sampleMasterSeed >>= fun seed =>
        (fun result => decide (SeedHitLog hit result.2 seed)) <$> trace)}[x = true] := by
      simp only [OracleComp.prEvent_bind_eq_tsum, probOutput_stopBefore_none, prEvent_map,
        decide_eq_true_eq]
      rfl
    _ = Pr{let x ← (trace >>= fun result =>
        (fun seed => decide (SeedHitLog hit result.2 seed)) <$> sampleMasterSeed)}[x = true] := by
      have hswap := OracleComp.EvalDistEq.bind_bind_swap sampleMasterSeed trace
        (fun seed result => (pure (decide (SeedHitLog hit result.2 seed)) : ProbComp Bool))
      simp only [bind_pure_comp] at hswap
      exact hswap.prEvent_eq (· = true)
    _ ≤ _ := by
      apply prEvent_bind_le_of_forall_le_of_support

      intro result hresult
      simp only [prEvent_map, decide_eq_true_eq]
      exact (probEvent_seedHitLog_le hhit result.2).trans
        (ENNReal.div_le_div
          (by exact_mod_cast traceHashes_length_le computation cache q hbound result hresult) le_rfl)

open scoped Classical in
theorem probEvent_random_cache_change_le {hit : HashInput → MasterSeed → Prop} (hhit : GuessBound hit)
    {α : Type} (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (fun input => hit input seed) (initial seed) cache)
    (q : Nat) (hbound : HashQueryBound computation cache q) (event : α → Prop) :
    Pr{let x ← sampleMasterSeed >>= fun seed => (simulateQ romImpl computation).run' (initial seed)}[event x] ≤
      Pr{let x ← (simulateQ romImpl computation).run' cache}[event x] + q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let stopped := fun seed =>
    (simulateQ romImpl (stopBefore (hashBad (fun input => hit input seed)) computation)).run' cache
  calc
    _ ≤ Pr{let x ← sampleMasterSeed >>= fun _ => (simulateQ romImpl computation).run' cache}[event x] +
        Pr{let x ← sampleMasterSeed >>= stopped}[x = none] := by
      simp only [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun seed =>
        (mul_le_mul' le_rfl (probEvent_cache_change_le (fun input => hit input seed)
          computation (initial seed) cache (hagree seed) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add (le_refl (Pr{let x ← (simulateQ romImpl computation).run' cache}[event x]))
        (probOutput_stopBefore_seed_le hhit computation cache q hbound)

end XmssSecurity.Seeded
