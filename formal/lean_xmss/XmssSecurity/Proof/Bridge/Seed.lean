module

public import XmssSecurity.Proof.EvalDistEq
public import XmssSecurity.Proof.Bridge.Reduction
public import XmssSecurity.Proof.Seeded.BudgetTransfer

@[expose] public section

/-!
# Eliminating the seed

The model's key generation never queries a derivation, so it runs over the programmed cache as over
the empty one, with the programmed entries laid on top. Those entries all name the scheme's seed `S`:
dropping them costs at most one `2^-256` guess of `S` per hash call after key generation.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

theorem run_progCache (seed : MasterSeed) (d : Derivations) :
    (simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d) =
      (fun p => (p.1, overlay (progCache seed d) p.2)) <$>
        (simulateQ randomOracle (honestRun d).withQueryLog).run ∅ := by
  conv_lhs => rw [← overlay_empty (progCache seed d)]
  exact OnlyQueries.run_overlay (honestRun_tweakable d).withQueryLog (E := progCache seed d)
    (fun x hx => progCache_tweakable hx) ∅

/-- The table game with the programmed derivations dropped from the cache. -/
noncomputable def cleanGame (adversary : LeanXmss.Security.Adversary) : ProbComp Bool := do
  let d ← drawDerivations
  let p ← (simulateQ randomOracle (honestRun d).withQueryLog).run ∅
  (simulateQ romImpl (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
    (modelPublicKey d p.1) (modelSecretKey d p.1))).run' p.2

theorem mem_support_progCache {seed : MasterSeed} {d : Derivations}
    {p : ((Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec) × QueryCache HashSpec}
    (hp : p ∈ support ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅)) :
    (p.1, overlay (progCache seed d) p.2) ∈
      support ((simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d)) := by
  rw [run_progCache, support_map]
  exact ⟨p, hp, rfl⟩

/-- The real budget, after key generation, from the clean cache. -/
theorem cleanBudget (adversary : LeanXmss.Security.Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (hbound : SeededBudget adversary q) (d : Derivations)
    {p : ((Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec) × QueryCache HashSpec}
    (hp : p ∈ support ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅)) :
    keygenQueries ≤ q ∧
      HashQueryBound (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary) (modelPublicKey d p.1)
        (modelSecretKey d p.1)) p.2 (q - keygenQueries) := by
  refine ⟨(afterKeygen_budget adversary q hbound 0 d p.1 _ (mem_support_progCache hp)).1, ?_⟩
  exact hashQueryBound_of_seed_caches guessBound_seedHit _ (q - keygenQueries) []
    (fun seed => overlay (progCache seed d) p.2) p.2 (by simp only [List.length_nil]; omega)
    (fun seed _ => agreeOutside_overlay_progCache seed d p.2)
    (fun seed _ => (afterKeygen_budget adversary q hbound seed d p.1 _ (mem_support_progCache hp)).2)

/-- Dropping the programmed entries costs a seed guess per hash call after key generation. -/
theorem tableGame_le_clean (adversary : LeanXmss.Security.Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (hbound : SeededBudget adversary q) :
    Pr{let x ← sampleMasterSeed >>= tableGame adversary}[x = true] ≤
      Pr{let x ← cleanGame adversary}[x = true] + ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hswap : (sampleMasterSeed >>= tableGame adversary) =ᵈ (do
      let d ← drawDerivations
      let p ← (simulateQ randomOracle (honestRun d).withQueryLog).run ∅
      let seed ← sampleMasterSeed
      (simulateQ romImpl (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
        (modelPublicKey d p.1) (modelSecretKey d p.1))).run' (overlay (progCache seed d) p.2)) := by
    unfold tableGame
    simp_rw [run_progCache, bind_map_left]
    refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
    apply EvalDistEq.bind_right
    intro d
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  refine (hswap.prEvent_eq (· = true)).trans_le ?_
  unfold cleanGame
  apply OracleComp.prEvent_bind_congr_le_add
  intro d _
  apply OracleComp.prEvent_bind_congr_le_add
  intro p hp
  exact probEvent_random_cache_change_le guessBound_seedHit _ (fun seed => overlay (progCache seed d) p.2) p.2
    (fun seed => agreeOutside_overlay_progCache seed d p.2) (q - keygenQueries)
    (cleanBudget adversary q hq hbound d hp).2 _

end XmssSecurity.Bridge
