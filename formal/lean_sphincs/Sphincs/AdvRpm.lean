module

public import Sphincs.Bridge
public import FORS.Reduction.AdvCountGame
public import Common.AdvBudget
public import Common.SphincsCost

@[expose] public section

/-!
# leanSPHINCS at the adversary's own count, in the random-permutation model

From upstream's model at the adversary's own count (`AdvBound c`: an adversary of `FORS.Security`
that itself makes at most `q` hash calls on every path forges with probability at most
`(q + c) / 2^127`; key generation, the signer and the final verification are not charged), the
route is the leanXMSS one (`XmssSecurity/Rpm.lean`):

* the model's experiment is the generic one (`experiment_eq`), so `AdvBound c` is
  `Common.SufCma.RomBoundAdv` for the model's scheme (`modelScheme_romBoundAdv`);
* the crate's copy wins as often (`Common.SufCma.StaticSwap.romBoundAdv`, the swap of
  `Sphincs/ModelRpm.lean`): `crateScheme_romBoundAdv`;
* `Common.SufCma.stronglyUnforgeable_of_romBoundAdv` moves it to the random-permutation model, the
  worst-case permutation calls of key generation, the signer and the verifier
  (`Common.SphincsCost`, stated for the statement's scheme and read back on the crate's copy
  through the maps, `crate_keygen_cost`, `crate_sign_cost`, `crate_verify_cost`) keeping the
  indifferentiability term below one unit: `crateScheme_stronglyUnforgeableAdv`;
* the statement's game is the crate's copy's against the adversary read through the maps
  (`Transport.forgeryGame_eq`), which neither adds a call of `π` or `π⁻¹` nor a signing request
  (`mapAdversary_cost`): `stronglyUnforgeableAdv_of_model`.
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace Sphincs.Model

attribute [local instance] params

/-- **Upstream's model at the adversary's own count**, at 127 bits with the constant `c`: every
adversary that itself makes at most `q` hash calls on every path, whatever the answers
(`FORS.Security.AdvCount.AdvHash`: a call of `H`; coins and signing requests free), forges with
probability at most `(q + c) / 2^127`. -/
def AdvBound (c : ℕ) : Prop :=
  ∀ (adversary : FORS.Security.Adversary) (q : ℕ),
    (∀ pk, (adversary.main pk).IsQueryBoundP FORS.Security.AdvCount.AdvHash q) →
      FORS.Security.forgeAdvantage adversary ≤ ((q : ℝ≥0∞) + c) / ((2 ^ 127 : ℕ) : ℝ≥0∞)

/-- A bound on a `0/1` weight is a bound on the number of queries it counts. -/
theorem isQueryBoundP_of_costAtMost {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : ι → Prop) [DecidablePred p] (w : ι → ℕ) (hw : ∀ t, w t = if p t then 1 else 0) :
    ∀ {oa : OracleComp spec α} {n : ℕ}, QueryCostAtMost oa w n → IsQueryBoundP oa p n := by
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

/-- **The model's bound in the form of `Common.SufCma.RomBoundAdv`**, at any number of signing
requests (upstream's game loses past its signature limit). -/
theorem modelScheme_romBoundAdv {c : ℕ} (h : AdvBound c) (maxRequests : ℕ) :
    RomBoundAdv modelScheme 127 c maxRequests := by
  intro q main hq _
  rw [← experiment_eq]
  exact h ⟨main⟩ q fun pk ↦ isQueryBoundP_of_costAtMost _ advHashCalls
    (by rintro ((_ | _) | _) <;> rfl) (hq pk)

/-- **The crate's copy at the adversary's own count**, from the model's. -/
theorem crateScheme_romBoundAdv {c : ℕ} (h : AdvBound c) (maxRequests : ℕ) :
    RomBoundAdv crateScheme 127 c maxRequests :=
  StaticSwap.romBoundAdv staticSwap Queries.Honest Queries.queriesIn_seededKeygen
    Queries.queriesIn_crateKeygen Queries.queriesIn_seededSign Queries.queriesIn_crateSign
    (modelScheme_romBoundAdv h maxRequests)

/-! ## The crate's copy over `π`: worst-case costs, read through the maps -/

local notation "σ" => schemeHashOverPermutation

theorem crate_keygen_cost (seed : FORS.MasterSeed) :
    QueryCostAtMost (crateScheme.overPermutation.generateKeys seed) permutationCallCost
      SphincsCost.KeyGenerationAndSigning.keygenCost := by
  have h := SphincsCost.sufCmaScheme_generateKeys_cost seed
  have heq : RandomPermutationModel.sufCmaScheme.generateKeys seed =
      (fun keys ↦ (ofModelPublicKey keys.1, keys.2)) <$>
        crateScheme.overPermutation.generateKeys seed :=
    (simulateQ_crateKeygen seed).symm
  rw [heq] at h
  exact (isQueryBound_map_iff _ _ _ _ _).1 h

theorem crate_sign_cost (seed : FORS.MasterSeed) (message : FORS.Message) :
    QueryCostAtMost (crateScheme.overPermutation.sign seed message) permutationCallCost
      SphincsCost.KeyGenerationAndSigning.signCost := by
  have h := SphincsCost.sufCmaScheme_sign_cost seed message
  have heq : RandomPermutationModel.sufCmaScheme.sign seed message =
      Option.map ofModelSignature <$> crateScheme.overPermutation.sign seed message :=
    (simulateQ_crateSign seed message).symm
  rw [heq] at h
  exact (isQueryBound_map_iff _ _ _ _ _).1 h

theorem crate_verify_cost (publicKey : FORS.PublicKey) (forgery : FORS.Forgery) :
    QueryCostAtMost (crateScheme.overPermutation.verify publicKey forgery) permutationCallCost
      SphincsCost.Verification.verifyCost := by
  have h := SphincsCost.sufCmaScheme_verify_cost (ofModelPublicKey publicKey)
    ⟨forgery.message, ofModelSignature forgery.signature⟩
  have heq : RandomPermutationModel.sufCmaScheme.verify (ofModelPublicKey publicKey)
      ⟨forgery.message, ofModelSignature forgery.signature⟩ =
      crateScheme.overPermutation.verify publicKey forgery := by
    have hv := (simulateQ_verify (ofModelPublicKey publicKey) forgery.message
      (ofModelSignature forgery.signature)).symm
    have hs : toModelSignature (ofModelSignature forgery.signature) = forgery.signature :=
      signatureEquiv.left_inv forgery.signature
    rw [hs] at hv
    exact hv
  rw [heq] at h
  exact h

/-- **The crate's copy over `π` at the adversary's own count**: `StronglyUnforgeable` with the
constant `c + 1`, up to `signatureLimit` signing requests. -/
theorem crateScheme_stronglyUnforgeableAdv {c : ℕ} (h : AdvBound c) :
    StronglyUnforgeable crateScheme.overPermutation signatureLimit (c + 1) 127 :=
  stronglyUnforgeable_of_romBoundAdv crateScheme (by norm_num) (crateScheme_romBoundAdv h _)
    crate_keygen_cost (fun seed message ↦ crate_sign_cost seed message) crate_verify_cost
    SphincsCost.total_le

/-! ## The statement's scheme, through the maps -/

/-- The map of an adversary against the statement's scheme to one against the crate's copy adds
no call of `π` or `π⁻¹` and no signing request: each query is forwarded, a signing answer read
through the map. -/
theorem mapAdversary_cost {PK₁ PK₂ Req Resp₁ Resp₂ F₁ F₂ : Type} (pkMap : PK₁ → PK₂)
    (φ : Resp₁ → Resp₂) (ψ : F₂ → F₁)
    (main : PK₂ → OracleComp (RandomPermutationOracles + (Req →ₒ Resp₂)) F₂)
    (w : RandomPermutationOracles.Domain ⊕ Req → ℕ) {n : ℕ} (pk : PK₁)
    (h : QueryCostAtMost (main (pkMap pk)) w n) :
    QueryCostAtMost (Transport.mapAdversary pkMap φ ψ main pk) w n := by
  unfold Transport.mapAdversary
  refine isWeightBound_map _ (isWeightBound_simulateQ _ w w (fun t ↦ ?_) h)
  rcases t with t | r
  · exact (isWeightBound_query _ _).mono le_rfl
  · exact isWeightBound_map _ ((isWeightBound_query _ _).mono le_rfl)

/-- **The statement's leanSPHINCS at the adversary's own count**, from the model's: the
statement's game is the crate's copy's against the mapped adversary, which makes the same calls of
`π` and `π⁻¹` and the same signing requests. -/
theorem stronglyUnforgeableAdv_of_model {c : ℕ} (h : AdvBound c) :
    StronglyUnforgeable RandomPermutationModel.sufCmaScheme signatureLimit (c + 1) 127 := by
  intro q main hq hn
  have hgame := Transport.forgeryGame_eq crateScheme RandomPermutationModel.sufCmaScheme
    ofModelPublicKey id (Option.map ofModelSignature) toModelForgery rfl
    (fun seed ↦ (simulateQ_crateKeygen seed).symm)
    (fun seed message ↦ (simulateQ_crateSign seed message).symm)
    (fun publicKey forgery ↦ (simulateQ_verify (ofModelPublicKey publicKey) forgery.message
      forgery.signature).symm) win_eq main
  have key := crateScheme_stronglyUnforgeableAdv h q
    (Transport.mapAdversary ofModelPublicKey (Option.map ofModelSignature) toModelForgery main)
    (fun pk ↦ mapAdversary_cost ofModelPublicKey (Option.map ofModelSignature) toModelForgery main
      _ pk (hq (ofModelPublicKey pk)))
    (fun pk ↦ mapAdversary_cost ofModelPublicKey (Option.map ofModelSignature) toModelForgery main
      _ pk (hn (ofModelPublicKey pk)))
  rw [forgeryGame_overPermutation, ← hgame] at key
  exact key

/-- A larger constant is a weaker bound. -/
theorem stronglyUnforgeable_mono_slack {Seed PK SK Req Resp F : Type}
    {scheme : Scheme Seed PK SK Req Resp F} {maxSignings slack slack' bits : ℕ}
    (h : StronglyUnforgeable scheme maxSignings slack bits) (hle : slack ≤ slack') :
    StronglyUnforgeable scheme maxSignings slack' bits := by
  intro q main hq hn
  refine (h q main hq hn).trans ?_
  gcongr

end Sphincs.Model
