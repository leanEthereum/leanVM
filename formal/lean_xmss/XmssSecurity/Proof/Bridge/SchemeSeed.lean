import XmssSecurity.Proof.Bridge.Reduction
import XmssSecurity.Proof.Seeded.BudgetTransfer
import LeanXmss.Bytes

/-!
# The scheme's seed

Key generation first hashes the key's seed `S_0` into the scheme's seed `S = H("leanXMSS" || S_0)`.
The answer is uniform, so the real game is the inner game from a uniform `S`, over a cache whose one
entry names `S_0`. Dropping that entry costs at most one `2^-256` guess of `S_0` per hash call after the
seed hash.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-- The input names the key's seed: it is the seed hash's input. -/
def KeySeedHit (input : HashInput) (keySeed : MasterSeed) : Prop :=
  input = LeanXmss.seedHashInput keySeed

theorem guessBound_keySeedHit : GuessBound KeySeedHit := by
  intro input
  classical
  by_cases hexists : ∃ keySeed, KeySeedHit input keySeed
  · obtain ⟨keySeed, hkey⟩ := hexists
    have hevent : KeySeedHit input = fun other => other = keySeed := by
      funext other
      exact propext ⟨fun h => LeanXmss.seedHashInput_injective (h.symm.trans hkey), fun h => h ▸ hkey⟩
    rw [hevent]
    simp [sampleMasterSeed, MasterSeed]
  · have hempty : KeySeedHit input = fun _ => False := by
      funext keySeed
      exact propext ⟨fun h => hexists ⟨keySeed, h⟩, False.elim⟩
    simp [hempty]

/-- The cache after the seed hash of `S_0` answered `S`. -/
def keySeedCache (keySeed seed : MasterSeed) : QueryCache HashSpec :=
  (∅ : QueryCache HashSpec).cacheQuery (LeanXmss.seedHashInput keySeed) seed

theorem agreeOutside_keySeedCache (keySeed seed : MasterSeed) :
    AgreeOutside (fun input => KeySeedHit input keySeed) (keySeedCache keySeed seed) ∅ :=
  fun _ hx => QueryCache.cacheQuery_of_ne _ _ hx

/-- The real game: sample `S_0`, hash it into `S`, then play the real game from `S`. -/
theorem gameCore_eq_seedHash (adversary : LeanXmss.Security.Adversary) :
    (LeanXmss.Security.gameCore adversary : OracleComp OracleWorld Bool) =
      (liftM sampleMasterSeed : OracleComp OracleWorld _) >>= fun keySeed =>
        liftM (OracleWorld.query (.inr (LeanXmss.seedHashInput keySeed))) >>= realAfterSeed adversary := by
  rw [gameCore_eq]
  congr 1

theorem run_seedHash (keySeed : MasterSeed) :
    (romImpl (.inr (LeanXmss.seedHashInput keySeed))).run ∅ =
      (fun seed => (seed, keySeedCache keySeed seed)) <$> ($ᵗ HashOutput : ProbComp HashOutput) :=
  QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)

theorem evalDist_sampleMasterSeed : 𝒟[sampleMasterSeed] = 𝒟[($ᵗ HashOutput : ProbComp HashOutput)] :=
  evalDist_ext fun seed => by
    unfold sampleMasterSeed
    rw [probOutput_uniformSample, probOutput_uniformSample (α := HashOutput)]
    rfl

/-- The real budget leaves `q - 1` hash calls after the seed hash, from every scheme seed. -/
theorem seededBudget (adversary : LeanXmss.Security.Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (hbound : LeanXmss.Security.HasHashQueryBound adversary q) : SeededBudget adversary q := by
  intro seed
  have hgame : HashQueryBound (LeanXmss.Security.gameCore adversary : OracleComp OracleWorld Bool) ∅ q := by
    simp only [HashQueryBound, simulateQ_countHashQueries]
    exact hbound
  rw [gameCore_eq_seedHash] at hgame
  refine hashQueryBound_of_seed_caches guessBound_keySeedHit _ (q - 1) [] (keySeedCache · seed) ∅
    (by simp only [List.length_nil]; omega) (fun keySeed _ => agreeOutside_keySeedCache keySeed seed)
    fun keySeed _ => ?_
  have hkey := hashQueryBound_of_sampling_bind sampleMasterSeed _ ∅ q hgame keySeed (by
    rw [mem_support_iff]
    unfold sampleMasterSeed
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
  exact (hashQueryBound_query_bind _ _ ∅ q hkey (seed, keySeedCache keySeed seed) (by
    rw [run_seedHash, support_map]
    exact ⟨seed, mem_support_uniformSample HashOutput, rfl⟩)).2

/-- Replacing the seed hash by a uniform `S` costs one guess of `S_0` per later hash call. -/
theorem forgeAdvantage_le_inner (adversary : LeanXmss.Security.Adversary) (q : Nat)
    (hbound : SeededBudget adversary q) :
    LeanXmss.Security.forgeAdvantage adversary ≤
      Pr[= true | (simulateQ romImpl (innerGame adversary)).run' ∅] +
        ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hadv : LeanXmss.Security.forgeAdvantage adversary =
      Pr[= true | (simulateQ romImpl (LeanXmss.Security.gameCore adversary : OracleComp OracleWorld Bool)).run' ∅] := by
    unfold LeanXmss.Security.forgeAdvantage LeanXmss.Security.experiment
    rw [← probOutput_countHashQueries, simulateQ_countHashQueries]
    rfl
  have hreal : 𝒟[(simulateQ romImpl (LeanXmss.Security.gameCore adversary : OracleComp OracleWorld Bool)).run' ∅] =
      𝒟[sampleMasterSeed >>= fun seed => sampleMasterSeed >>= fun keySeed =>
        (simulateQ romImpl (realAfterSeed adversary seed)).run' (keySeedCache keySeed seed)] := by
    rw [gameCore_eq_seedHash, run'_lift_sample_bind]
    simp only [run'_query_bind, run_seedHash, bind_map_left]
    rw [evalDist_bind_bind_swap, evalDist_bind, ← evalDist_sampleMasterSeed, ← evalDist_bind]
  rw [hadv, probOutput_def, hreal, ← probOutput_def, innerGame, run'_lift_sample_bind,
    ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_congr_le_add
  intro seed _
  exact probEvent_random_cache_change_le guessBound_keySeedHit _ (keySeedCache · seed) ∅
    (fun keySeed => agreeOutside_keySeedCache keySeed seed) (q - 1) (hbound seed) _

end XmssSecurity.Bridge
