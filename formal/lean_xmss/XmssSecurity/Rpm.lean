module

public import LeanXmss.Statement
public import Common.Signature
public import Statement.LeanXmss
public import Common.WithHash
public import XmssSecurity.Proof.OwnBridge
public import Common.AdvBudget
public import Common.XmssCost
public import Common.WithHashBridge
public import Common.SeedKey

@[expose] public section

/-!
# leanXMSS in the random-permutation model

The ROM theorem at the adversary's own count (`Bridge.leanXmss_security`: at most `q` hash
calls of the adversary itself and `lifetime` signing requests, success at most
`(q + (2^10 - 1)) / 2^127`) is `Common.SufCma.RomBoundAdv` for the hash-query scheme
(`romBoundAdv`), passes to the crate's key, the seed `S_0` kept (`romBoundAdvFromSeed`), and moves
to the random-permutation model by `Common.SufCma.stronglyUnforgeable_of_romBoundAdv`, whose
indifferentiability term the worst-case costs of key generation, the signer and the verifier
(`Common.XmssCost`) keep below one unit `2^-127`.
-/
open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace XmssSecurity

/- A weight bound of a concrete game must not be unfolded: it recurses through the whole game. -/
attribute [local irreducible] QueryCostAtMost

/-- The leanXMSS ROM experiment is the generic one. -/
theorem experiment_eq_romExperiment
    (main : HashSig.PublicKey →
      OracleComp (LeanXmss.OracleWorld + LeanXmss.SigningOracleSpec) LeanXmss.Forgery) :
    LeanXmss.Security.experiment ⟨main⟩ = romExperiment
        LeanXmss.RandomPermutationModel.schemeWithHash main := by
  have h : LeanXmss.Security.countedOracle = countedImpl := by
    unfold LeanXmss.Security.countedOracle countedImpl
    congr 1
  unfold LeanXmss.Security.experiment romExperiment
  rw [h]
  rfl

/-- A bound on a `0/1` weight is a bound on the number of queries it counts. -/
theorem isQueryBoundP_of_costAtMost {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : ι → Prop) [DecidablePred p] (w : ι → ℕ) (hw : ∀ t, w t = if p t then 1 else 0) :
    ∀ {oa : OracleComp spec α} {n : ℕ}, Common.QueryCostAtMost oa w n → IsQueryBoundP oa p n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro n _; trivial
  | query_bind t k ih =>
    intro n h
    rw [isWeightBound_query_bind_iff] at h
    rw [isQueryBoundP_query_bind_iff]
    have hk := fun u ↦ ih u (h.2 u)
    rw [hw t] at h hk
    by_cases hp : p t
    · simp only [hp, ite_true] at h hk ⊢
      exact ⟨Or.inr (by omega), hk⟩
    · simp only [hp, ite_false, Nat.sub_zero, not_false_eq_true, true_or, true_and] at h hk ⊢
      exact hk

/-- **The ROM theorem at the adversary's own count, in the form of
`Common.SufCma.RomBoundAdv`.** -/
theorem romBoundAdv : RomBoundAdv LeanXmss.RandomPermutationModel.schemeWithHash 127
    Bridge.romAdversarySlack LeanXmss.lifetime := by
  intro q main hq hr
  rw [← experiment_eq_romExperiment]
  exact Bridge.leanXmss_security q ⟨main⟩
    (fun pk ↦ isQueryBoundP_of_costAtMost _ advHashCalls (by rintro ((_ | _) | _) <;> rfl) (hq pk))
    (fun pk ↦ isQueryBoundP_of_costAtMost _ requestCalls (by rintro (_ | _) <;> rfl) (hr pk))

/-- leanXMSS's signer derives `S` again from the kept seed `S_0`: in the random-oracle model, after
key generation's derivation of `S` and `P`, a cache hit that returns them. -/
theorem keptKey_reruns : LeanXmss.RandomPermutationModel.keptKey.Reruns := by
  intro seed c z hz c' hc'
  simp only [LeanXmss.RandomPermutationModel.keptKey,
    LeanXmss.KeyGenerationAndSigning.deriveSchemeSeedKey] at hz
  rw [liftM_bind, romRun_bind, mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  have hle : w.2 ≤ z.2 := le_of_mem_support_run _ _ hz
  have hkey : z.1 = ⟨w.1, z.1.parameter⟩ := by
    have h := (mem_support_liftM_world _ _).mp (KeptKey.fst_mem_support_romRun' hz)
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
    obtain ⟨parameter, -, h⟩ := h
    rw [h]
  simp only [LeanXmss.RandomPermutationModel.keptKey,
    LeanXmss.KeyGenerationAndSigning.rederiveSchemeSeedKey, liftM_bind, romRun_bind,
    run_rerun _ (noCoins_liftM _) c hw c' (le_trans hle hc'), pure_bind]
  rw [← hkey]
  rfl

/-- The ROM theorem at the adversary's own count for the crate's secret key, the seed `S_0` and the
public parameter, whose signer derives `S` again at each signature: those calls hit the random
oracle's cache (`Common.SufCma.KeptKey`). -/
theorem romBoundAdvFromSeed : RomBoundAdv LeanXmss.RandomPermutationModel.schemeWithHashFromSeed 127
    Bridge.romAdversarySlack LeanXmss.lifetime :=
  LeanXmss.RandomPermutationModel.keptKey.romBoundAdv keptKey_reruns romBoundAdv

/-- **leanXMSS in the random-permutation model**: an adversary that itself makes at most `q` calls of
`π` and `π⁻¹` and at most `lifetime` signing requests forges with probability at most
`(q + 2^10) · 2^-127`. The statement's scheme is the hash-query scheme over `π`
(`LeanXmss.RandomPermutationModel.scheme_eq`), whose key generation, signer and verifier make at
most `Common.XmssCost.keygenCost`, `signCost` and `verifyCost` permutation calls. -/
theorem leanXmss_rpm_security : LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable := by
  apply LeanXmss.RandomPermutationModel.leanXmssStronglyUnforgeable_of_overPermutation
  have h := stronglyUnforgeable_of_romBoundAdv LeanXmss.RandomPermutationModel.schemeWithHashFromSeed
    (by norm_num) romBoundAdvFromSeed
    (fun seed ↦ LeanXmss.RandomPermutationModel.scheme_eq ▸
      Common.XmssCost.sufCmaScheme_generateKeys_cost seed)
    (fun sk r ↦ LeanXmss.RandomPermutationModel.scheme_eq ▸
      Common.XmssCost.sufCmaScheme_sign_cost sk r)
    (fun pk f ↦ LeanXmss.RandomPermutationModel.scheme_eq ▸
      Common.XmssCost.sufCmaScheme_verify_cost pk f)
    Common.XmssCost.total_le
  exact h

end XmssSecurity
