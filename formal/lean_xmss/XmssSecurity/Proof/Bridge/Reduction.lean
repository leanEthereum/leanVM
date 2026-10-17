import XmssSecurity.Proof.Bridge.Game
import XmssSecurity.Proof.Seeded.Presampling

/-!
# From the real experiment to the table game

Presampling every derivation and the model's key generation before the real experiment changes
nothing; afterwards the real key generation is cached and the rest of the real game erases to the
model's game with the table signer. The real budget `q` leaves `q - K` hash calls after key
generation.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-- The model's key generation over the table, after programming the derivations. -/
noncomputable def preparation (seed : MasterSeed) :
    OracleComp HashSpec (Derivations × ((Digest × (TopIndex → Option (Randomness × Encoding))) ×
      QueryLog HashSpec)) := do
  let d ← programDerivations seed
  let result ← (honestRun d).withQueryLog
  return (d, result)

theorem run_preparation (seed : MasterSeed) :
    𝒟[(simulateQ randomOracle (preparation seed)).run ∅] =
      𝒟[do
        let d ← drawDerivations
        let r ← (simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d)
        pure ((d, r.1), r.2)] := by
  unfold preparation
  rw [simulateQ_bind, StateT.run_bind, evalDist_programDerivations_draw]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]

theorem mem_support_preparation (seed : MasterSeed) (d : Derivations)
    (r : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec)
    (cache : QueryCache HashSpec)
    (hr : (r, cache) ∈ support ((simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d))) :
    ((d, r), cache) ∈ support ((simulateQ randomOracle (preparation seed)).run ∅) := by
  rw [mem_support_iff_of_evalDist_eq (run_preparation seed), mem_support_bind_iff]
  refine ⟨d, mem_support_drawDerivations d, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨(r, cache), hr, by simp⟩

/-- The table game reached from a seed: the derivations drawn, the model key prepared from the
programmed cache, then the model's game with the table signer. -/
noncomputable def tableGame (adversary : LeanXmss.Security.Adversary) (seed : MasterSeed) : ProbComp Bool := do
  let d ← drawDerivations
  let r ← (simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d)
  (simulateQ romImpl (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
    (modelPublicKey d r.1) (modelSecretKey d r.1))).run' r.2

/-- The real key generation, in the model's oracle type. -/
def realKeygen (seed : MasterSeed) : OracleComp HashSpec (LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) :=
  LeanXmss.Seeded.keygenFromSeed seed

/-- The real game after the seed. -/
noncomputable def realAfterSeed (adversary : LeanXmss.Security.Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool :=
  (liftM (realKeygen seed) : OracleComp OracleWorld _) >>= fun keys => realRest adversary keys.1 keys.2

theorem gameCore_eq' (adversary : LeanXmss.Security.Adversary) :
    (LeanXmss.Security.gameCore adversary : OracleComp OracleWorld Bool) =
      (liftM sampleMasterSeed : OracleComp OracleWorld _) >>= realAfterSeed adversary := rfl

theorem erases_afterKeygen (adversary : LeanXmss.Security.Adversary) {seed : MasterSeed} {d : Derivations}
    {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
    {cache : QueryCache HashSpec} (h : Prepared seed d result cache) :
    Erases (worldKnown cache) (realAfterSeed adversary seed)
      (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary) (modelPublicKey d result)
        (modelSecretKey d result)) :=
  (erases_pure_of_resolves (computation := realKeygen seed) h.realKeygen).lift_hash.bind_known _ _
    (h.erases_rest adversary)

theorem lift_hash_romImpl {α : Type} (c : OracleComp HashSpec α) :
    simulateQ romImpl (liftM c : OracleComp OracleWorld α) = simulateQ randomOracle c :=
  QueryImpl.simulateQ_add_liftM_right _ _ c

/-- The real experiment's winning distribution is the table game's. -/
theorem evalDist_realGame (adversary : LeanXmss.Security.Adversary) :
    𝒟[(simulateQ romImpl (LeanXmss.Security.gameCore adversary : OracleComp OracleWorld Bool)).run' ∅] =
      𝒟[sampleMasterSeed >>= tableGame adversary] := by
  rw [gameCore_eq', run'_lift_sample_bind]
  apply evalDist_bind_congr'
  intro seed
  rw [evalDist_presample_computation _ (liftM (preparation seed) : OracleComp OracleWorld _) ∅,
    lift_hash_romImpl, evalDist_bind, run_preparation, ← evalDist_bind]
  unfold tableGame
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr'
  intro d
  apply evalDist_bind_congr
  intro r hr
  have h := prepared_of_mem seed d r.1 r.2 hr
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map,
    (erases_afterKeygen adversary h).evalDist_run r.2 le_rfl]

theorem probOutput_countHashQueries (computation : OracleComp OracleWorld Bool) :
    Pr[fun result => result.1 = true | (simulateQ romImpl (countHashQueries computation)).run' ∅] =
      Pr[= true | (simulateQ romImpl computation).run' ∅] := by
  have h := congrArg (fun c : OracleComp OracleWorld Bool => (simulateQ romImpl c).run' ∅)
    (countHashQueries_forget computation)
  simp only [simulateQ_map, StateT.run'_map'] at h
  rw [← h]
  simpa only [probEvent_eq_eq_probOutput, Function.comp_def] using
    (probEvent_map (mx := (simulateQ romImpl (countHashQueries computation)).run' ∅) (f := Prod.fst)
      (q := fun result => result = true)).symm

/-- The real experiment's advantage is the table game's winning probability. -/
theorem forgeAdvantage_eq_tableGame (adversary : LeanXmss.Security.Adversary) :
    LeanXmss.Security.forgeAdvantage adversary = Pr[= true | sampleMasterSeed >>= tableGame adversary] := by
  unfold LeanXmss.Security.forgeAdvantage LeanXmss.Security.experiment
  rw [probOutput_def, ← evalDist_realGame, ← probOutput_def, ← probOutput_countHashQueries,
    simulateQ_countHashQueries]
  rfl

/-! ## Budgets -/

theorem experiment_eq (adversary : LeanXmss.Security.Adversary) :
    LeanXmss.Security.experiment adversary =
      (simulateQ countedRomImpl ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>=
        realAfterSeed adversary)).run.run' ∅ :=
  rfl

theorem hashQueryBound_real (adversary : LeanXmss.Security.Adversary) (q : Nat)
    (hbound : LeanXmss.Security.HasHashQueryBound adversary q) :
    HashQueryBound ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>= realAfterSeed adversary) ∅ q := by
  have h : HashQueryBound ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>= realAfterSeed adversary) ∅ q ↔
      ∀ result ∈ support ((simulateQ countedRomImpl ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>=
        realAfterSeed adversary)).run.run' ∅), result.2 ≤ q := by
    simp only [HashQueryBound, simulateQ_countHashQueries]
    rfl
  rw [h, ← experiment_eq]
  exact hbound

/-- The real budget `q` leaves `q - K` hash calls for the table game after key generation. -/
theorem afterKeygen_budget (adversary : LeanXmss.Security.Adversary) (q : Nat)
    (hbound : LeanXmss.Security.HasHashQueryBound adversary q) (seed : MasterSeed) (d : Derivations)
    (r : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec)
    (cache : QueryCache HashSpec)
    (hr : (r, cache) ∈ support ((simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d))) :
    keygenQueries ≤ q ∧
      HashQueryBound (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary) (modelPublicKey d r)
        (modelSecretKey d r)) cache (q - keygenQueries) := by
  have hgame := hashQueryBound_real adversary q hbound
  have hseed : HashQueryBound (realAfterSeed adversary seed) ∅ q :=
    hashQueryBound_of_sampling_bind sampleMasterSeed _ ∅ q hgame seed (by
      rw [mem_support_iff]
      unfold sampleMasterSeed
      rw [probOutput_uniformSample]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
  have hprep := hashQueryBound_after_preparation _ (liftM (preparation seed) : OracleComp OracleWorld _) ∅ q
    hseed ((d, r), cache) (by
      rw [lift_hash_romImpl]
      exact mem_support_preparation seed d r cache hr)
  have h := prepared_of_mem seed d r cache hr
  have hrun := run_countHashQueries_lift_of_resolves (c := realKeygen seed) (queryCount_realKeygen seed)
    h.realKeygen
  have hfirst := hashQueryBound_bind (realKeygen seed) (fun keys => realRest adversary keys.1 keys.2) cache q
    hprep (((⟨r.1.1, d.parameter⟩, ⟨seed, d.parameter, r.1.1⟩), keygenQueries), cache) (by rw [hrun]; simp)
  exact ⟨hfirst.1, (h.erases_rest adversary).hashQueryBound cache le_rfl _ hfirst.2⟩

end XmssSecurity.Bridge
