module

public import XmssSecurity.Proof.Bridge.Model
public import XmssSecurity.Proof.Bridge.SchemeSeed
public import XmssSecurity.Proof.OwnModel
public import XmssSecurity.Proof.OwnReal

@[expose] public section

/-!
# The adversary's own count, from the statement to the model

The translated, memoized adversary makes no more hash calls of its own than the statement's: the
translation forwards each hash query once, and memoization forwards every base query once.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-- At most `2^128` guesses of a 256-bit seed cost one unit. -/
theorem guesses_le {n : Nat} (hn : n ≤ 2 ^ 128) :
    (n : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  calc
    _ ≤ ((2 ^ 128 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := ENNReal.div_le_div (by exact_mod_cast hn) le_rfl
    _ = ((2 ^ 128 : Nat) : ℝ≥0∞) / (((2 ^ 128 : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)) := by norm_num
    _ = _ := by
      simpa only [mul_one] using ENNReal.mul_div_mul_left 1 ((2 ^ 128 : Nat) : ℝ≥0∞)
        (c := ((2 ^ 128 : Nat) : ℝ≥0∞)) (by norm_num) (ENNReal.natCast_ne_top _)

/-- Memoization forwards each base query once and adds none. -/
theorem memoize_own {ι : Type} {base : OracleSpec ι} {Request Answer : Type} [DecidableEq Request]
    (p : ι → Prop) [DecidablePred p] {α : Type}
    (computation : OracleComp (base + (Request →ₒ Answer)) α) :
    ∀ (n : ℕ) (cache : QueryCache (Request →ₒ Answer)), IsQueryBoundP computation (OnWorld p) n →
      IsQueryBoundP (memoize computation cache) (OnWorld p) n := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro n cache _; exact isQueryBoundP_pure _ _ _
  | query_bind input next ih =>
      intro n cache h
      rw [isQueryBoundP_query_bind_iff] at h
      cases input with
      | inl input =>
          rw [memoize_base, isQueryBoundP_query_bind_iff]
          exact ⟨h.1, fun answer => ih answer _ cache (h.2 answer)⟩
      | inr request =>
          rw [memoize_request]
          have hnext := fun answer => h.2 answer
          rw [ite_eq_right (not_onWorld_inr p request)] at hnext
          split
          · exact ih _ n cache (hnext _)
          · rw [isQueryBoundP_query_bind_iff, ite_eq_right (not_onWorld_inr p request)]
            exact ⟨Or.inl (not_onWorld_inr p request), fun answer => ih answer n _ (hnext answer)⟩

/-- The translation forwards each hash query once and adds none. -/
theorem adversaryImpl_own {α : Type}
    (computation : OracleComp (LeanXmss.OracleWorld + LeanXmss.SigningOracleSpec) α) :
    ∀ n : ℕ, IsQueryBoundP computation (OnWorld IsWorldHashQuery) n →
      IsQueryBoundP (simulateQ adversaryImpl computation) (OnWorld IsWorldHashQuery) n := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro n _; exact isQueryBoundP_pure _ _ _
  | query_bind input next ih =>
      intro n h
      rw [isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind]
      cases input with
      | inl input =>
          change IsQueryBoundP (liftM ((OracleWorld + SigningSpec).query (.inl input)) >>= fun u =>
            simulateQ adversaryImpl (next u)) _ n
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨h.1, fun answer => ih answer _ (h.2 answer)⟩
      | inr request =>
          change IsQueryBoundP ((Option.map (toRealSig request.leafIndex) <$>
            liftM ((OracleWorld + SigningSpec).query (.inr (toModelReq request)))) >>= fun u =>
              simulateQ adversaryImpl (next u)) _ n
          rw [map_eq_bind_pure_comp, bind_assoc, isQueryBoundP_query_bind_iff,
            ite_eq_right (not_onWorld_inr _ _)]
          have hnext := fun answer => h.2 answer
          rw [ite_eq_right (not_onWorld_inr _ _)] at hnext
          exact ⟨Or.inl (not_onWorld_inr _ _), fun answer => by
            simpa only [Function.comp_apply, pure_bind] using ih _ n (hnext _)⟩

/-- The model adversary's own hash calls are at most the statement adversary's. -/
theorem modelAdversary_own (adversary : LeanXmss.Security.Adversary) (q : Nat)
    (hadv : LeanXmss.Security.AdversaryHashQueryBound adversary q) :
    OwnHashBound (modelAdversary adversary) q := by
  intro publicKey
  refine (isQueryBoundP_congr_pred isAdvHashAction_iff).mpr ?_
  refine memoize_own IsWorldHashQuery _ q ∅ ?_
  change IsQueryBoundP (toModelForgery <$> simulateQ adversaryImpl (adversary.main (toRealPk publicKey))) _ q
  rw [isQueryBoundP_map_iff]
  exact adversaryImpl_own _ q ((isQueryBoundP_congr_pred realOwn_iff).mp (hadv _))

/-! ## The bound -/

/-- The constant of the bound at the adversary's own count: half the model's (the verification's
calls in each lane and lane 1's forgery probes) plus the two seed guesses. -/
def romAdversaryConstant : Nat := 530

theorem romAdversaryConstant_eq : 2 * romAdversaryConstant = ownModelSlack + 2 := by
  rw [ownModelSlack_eq]; rfl

/-- The real game's whole budget at own count `q` and a request per leaf index. -/
def realGameCalls (q : Nat) : Nat := keygenQueries + (q + LeanXmss.lifetime * realSignCalls) + realVerifyCalls

theorem realGameCalls_le (q : Nat) (hq : q < 2 ^ 127) : realGameCalls q ≤ 2 ^ 128 := by
  have h : keygenQueries + LeanXmss.lifetime * realSignCalls + realVerifyCalls < 2 ^ 127 := by
    norm_num [keygenQueries, realSignCalls, realLayerCalls, nodeQueries, realVerifyCalls, realLayerVerifyCalls,
      LeanXmss.lifetime, LeanXmss.layerCount, LeanXmss.layerHeight]
  simp only [realGameCalls]
  omega

theorem final_arithmetic (q Q : Nat) (hQ : Q ≤ 2 ^ 128) :
    ((2 * q + ownModelSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
      ((Q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
        ((Q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
      ((q + romAdversaryConstant : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hhalf : ((2 * (q + romAdversaryConstant) : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) =
      ((q + romAdversaryConstant : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
    rw [show (2 ^ 128 : Nat) = 2 * 2 ^ 127 by norm_num, Nat.cast_mul, Nat.cast_mul]
    exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)
  calc
    _ ≤ ((2 * q + ownModelSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
      add_le_add (add_le_add le_rfl (guesses_le (by omega))) (guesses_le (by omega))
    _ = ((2 * q + ownModelSlack + 1 + 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
      rw [← ENNReal.add_div, ← ENNReal.add_div, Nat.cast_succ, Nat.cast_succ]
    _ = ((2 * (q + romAdversaryConstant) : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
      rw [show 2 * q + ownModelSlack + 1 + 1 = 2 * (q + romAdversaryConstant) by
        have := romAdversaryConstant_eq
        omega]
    _ = _ := hhalf

theorem leanXmss_security_lt (q : Nat) (hq : q < 2 ^ 127) (adversary : LeanXmss.Security.Adversary)
    (hadv : LeanXmss.Security.AdversaryHashQueryBound adversary q)
    (hsign : LeanXmss.Security.SigningRequestBound adversary LeanXmss.lifetime) :
    LeanXmss.Security.forgeAdvantage adversary ≤
      ((q + romAdversaryConstant : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hQ := realGameCalls_le q hq
  set Q := realGameCalls q
  have hreal : LeanXmss.Security.HasHashQueryBound adversary Q :=
    realGame_hasHashQueryBound adversary q LeanXmss.lifetime hadv hsign
  have hseeded := seededBudget adversary Q (by omega) hreal
  have hlanes := concreteScheme_security q (modelAdversary adversary) (modelAdversary_own adversary q hadv) hq
  calc LeanXmss.Security.forgeAdvantage adversary
      ≤ Pr{let x ← (simulateQ romImpl (innerGame adversary)).run' ∅}[x = true] +
        ((Q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := forgeAdvantage_le_inner adversary Q hseeded
    _ = Pr{let x ← sampleMasterSeed >>= tableGame adversary}[x = true] +
        ((Q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by rw [innerGame_eq_tableGame]
    _ ≤ Pr{let x ← cleanGame adversary}[x = true] +
        ((Q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
          ((Q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
      add_le_add (tableGame_le_clean adversary Q (by omega) hseeded) le_rfl
    _ ≤ Pr{let x ← refGame adversary}[x = true] +
        ((Q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
          ((Q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
      add_le_add (add_le_add (cleanGame_le_ref adversary) le_rfl) le_rfl
    _ = forgeAdvantage Concrete.scheme (modelAdversary adversary) +
        ((Q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
          ((Q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by rw [refGame_eq]
    _ ≤ ((2 * q + ownModelSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((Q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
          ((Q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := add_le_add (add_le_add hlanes le_rfl) le_rfl
    _ ≤ _ := final_arithmetic q Q hQ

/-- The published slack, `2^10 - 1`: room above the proof's `530`, so that the slack plus the
sponge's one unit in the random-permutation model is `2^10` (`LeanXmss.RandomPermutationModel.securitySlack`). -/
def romAdversarySlack : Nat := 2 ^ 10 - 1

/-- **leanXMSS at the adversary's own hash calls**, for every own count `q`. -/
theorem leanXmss_security (q : Nat) (adversary : LeanXmss.Security.Adversary)
    (hadv : LeanXmss.Security.AdversaryHashQueryBound adversary q)
    (hsign : LeanXmss.Security.SigningRequestBound adversary LeanXmss.lifetime) :
    LeanXmss.Security.forgeAdvantage adversary ≤
      ((q : ℝ≥0∞) + romAdversarySlack) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  by_cases hq : q < 2 ^ 127
  · refine (leanXmss_security_lt q hq adversary hadv hsign).trans (ENNReal.div_le_div ?_ le_rfl)
    rw [Nat.cast_add]
    exact add_le_add le_rfl (by simp only [romAdversaryConstant, romAdversarySlack]; norm_num)
  · calc
      LeanXmss.Security.forgeAdvantage adversary ≤ 1 := prEvent_le_one _
      _ = ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div ((Nat.cast_le.2 (Nat.le_of_not_gt hq)).trans le_self_add) le_rfl

end XmssSecurity.Bridge
