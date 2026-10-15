import Sphincs.BridgeSatW
import Sphincs.BridgeSignerForest
import Sphincs.BridgeScan

/-! The bounds of the scan signer `R = R0 + i`, weighted by the final survival weight. The
message-digest blocks are untargeted, so their reads keep the weight; everything after the digest
read of the final assembly lowers it in expectation. Each bound of `BridgeScan` therefore holds with
the integrand multiplied by the final weight and the walk value multiplied by the initial weight. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.GraphView

open SphincsFors.Security
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForestSigner Sphincs.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

section LoopSW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- **Final assembly, one cached block, weighted.** -/
theorem finish_bound₁W (randomness : Randomness)
    (hparse : model.parse (blk parameter data message randomness) = none)
    (state : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput)
    (hc0 : state.cache (blk parameter data message randomness) = some u0)
    (g : HashOutput → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message randomness) budget state] *
        (weight tg initial out.2 * (if out.1.1.isSome then
          (out.2.cache (blk parameter data message randomness)).elim 0 g else 0)) ≤
      weight tg initial state * g u0 := by
  rw [finishCostSource_eq, interp_ordinary]
  split_ifs with h0
  · rw [ordinaryStep, hparse]
    simp only
    rw [readOutside_cached _ state u0 hc0, pure_bind, tsum_probOutput_map_mul]
    refine interp_weight_mul_leW tg initial model _ _ state _ _ fun out hout => ?_
    have hk0 := interp_avoids_cache tg initial model _ _ (avoids_mono (fun x hx => by
        subst hx; exact msgInput_digestInput parameter data.root message randomness)
      (avoids_finishRest parameter data message randomness _)) _ state out hout
      (blk parameter data message randomness) rfl
    split_ifs
    · rw [hk0, hc0]; rfl
    · exact bot_le
  · rw [tsum_probOutput_pure_mul]
    simp

/-- The arithmetic of one fresh trial: it lands with probability `landing` on a uniform view, and
the scan goes on otherwise. -/
theorem trials_sum_le (gf : Lifetime.KeptDigestView → ℝ≥0∞) (bound : ℝ≥0∞) :
    ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then gf (viewOf u0) else bound) ≤
      ForestPrice.landing * Domination.freshAvg Finset.univ gf + (1 - ForestPrice.landing) * bound := by
  have hsplit : (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then gf (viewOf u0) else bound)) =
      (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0)) +
      bound * ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then 0 else 1) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun u0 => ?_
    split_ifs
    · simp
    · simp [mul_comm]
  rw [hsplit, unlanded_mass parameter, fresh_view_mean parameter gf, mul_comm bound]

/-- **One trial of the scan, weighted**, with any continuation. -/
theorem trial_boundSW
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data message ρ) = .none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hVabort : ∀ s', V none s' = 0)
    (hVfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.1 out.2 ≤ (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0))
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (cont : OracleComp CostSpec (Option Signature))
    (hih : ∀ s', Related parameter data message reference s' →
      (∀ x, x ≠ blk parameter data message ρ → s'.cache x = state.cache x) → ∀ b,
        ∑' out, Pr[= out | interp tg initial model cont b s'] *
          (weight tg initial out.2 * V out.1.1 out.2) ≤ weight tg initial s' * bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        (weight tg initial out.2 * V out.1.1 out.2) ≤
      weight tg initial state * (state.cache (blk parameter data message ρ)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then gf (viewOf u0) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          (weight tg initial out.2 * V out.1.1 out.2) ≤
        weight tg initial s' * pairWeight parameter data message reference gf gp ρ u0 := by
    intro s' u0 b hrel' hs'
    refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) (finish_bound₁W tg initial model parameter data message ρ
      (hparse ρ) s' u0 hs' _ b)
    by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
    · exact mul_le_mul_right (mul_le_mul_right (hVfin s' u0 b hrel' hs' out hout) _) _
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          have href : reference.cache (blk parameter data message ρ) = some u0 := by
            rcases hrel ρ with h | ⟨_, u, hu, hnl⟩
            · rw [← h]; exact hc
            · rw [hc] at hu; cases hu; exact absurd hl hnl
          refine le_trans (hfinish state u0 _ (fun ρ' _ => hrel ρ') hc) (le_of_eq ?_)
          simp [pairWeight, poolValue, href, hl]
        · rw [if_neg hl, if_neg hl]
          exact hih state hrel (fun _ _ => rfl) _
    | none =>
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        have href : reference.cache (blk parameter data message ρ) = none := by
          rcases hrel ρ with h | ⟨h, _⟩
          · rw [← h]; exact hc
          · exact h
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun u0 => ?_
        rw [mul_left_comm]
        refine mul_le_mul_right ?_ _
        have hw : weight tg initial (state.store (blk parameter data message ρ) u0) = weight tg initial state :=
          weight_store_untargetedW tg initial state _ u0 (hkind ρ)
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          refine le_trans (hfinish _ u0 _ (fun ρ' hρ' => by
              rw [show (state.store (blk parameter data message ρ) u0).cache (blk parameter data message ρ') =
                state.cache (blk parameter data message ρ') from
                store_cache_ne state _ _ (blk_ne_of_ne parameter data message hρ') u0]
              exact hrel ρ')
            (by simp [DebtState.store])) (le_of_eq ?_)
          rw [hw]
          simp only [pairWeight, href, if_true, if_pos hl]
        · rw [if_neg hl, if_neg hl]
          have h := hih _ (related_store parameter data message reference state hrel ρ hc u0 hl)
            (fun x hx => store_cache_ne state _ x hx u0) (budget - 1)
          rwa [hw] at h
  · rw [tsum_probOutput_pure_mul]
    rw [hVabort, mul_zero]
    exact zero_le

/-- **The scan from a start, weighted.** The weighted weight of the signed pair is at most the
initial weight times the walk value over the reference cache. The state may differ from the
reference by rejected blocks behind the start. -/
theorem loop_boundSW
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data message ρ) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hVabort : ∀ s', V none s' = 0)
    (hVnone : ∀ s' : DebtState HashInput HashOutput Coordinate, Related parameter data message reference s' →
      V (some none) s' = 0)
    (hVfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.1 out.2 ≤ (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0)) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      (∀ i, i < attempts → state.cache (blk parameter data message ((nextRand ^ i) ρ)) =
        reference.cache (blk parameter data message ((nextRand ^ i) ρ))) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts ρ) budget state] *
          (weight tg initial out.2 * V out.1.1 out.2) ≤
        weight tg initial state * walk nextRand ForestPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ := by
  intro attempts
  induction attempts with
  | zero =>
      intro _ budget state ρ hrel _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        (weight tg initial out.2 * V out.1.1 out.2) ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change weight tg initial state * V (some none) state ≤ _
      rw [hVnone state hrel, mul_zero]
      exact bot_le
  | succ attempts ih =>
      intro hA budget state ρ hrel hahead
      rw [signCostSourceLoop_succ]
      have hnext : ∀ s', Related parameter data message reference s' →
          (∀ x, x ≠ blk parameter data message ρ → s'.cache x = state.cache x) → ∀ b,
          ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts (nextRand ρ)) b s'] *
            (weight tg initial out.2 * V out.1.1 out.2) ≤
          weight tg initial s' * walk nextRand ForestPrice.landing (stOf parameter data message reference)
            (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts
            (nextRand ρ) := by
        intro s' hrel' hsame b
        refine ih (Nat.le_of_succ_le hA) b s' (nextRand ρ) hrel' fun i hi => ?_
        have hpow : (nextRand ^ i) (nextRand ρ) = (nextRand ^ (i + 1)) ρ := by
          rw [pow_succ, Equiv.Perm.mul_apply]
        rw [hpow, hsame _ (blk_ne_of_ne parameter data message
          (nextRand_pow_ne ρ (i + 1) (Nat.succ_pos i) (by omega)))]
        exact hahead (i + 1) (Nat.succ_lt_succ hi)
      refine le_trans (trial_boundSW tg initial model parameter data message hparse hkind reference ρ gf gp V hVabort
        (hVfin ρ) _ state hrel _ hnext budget) (mul_le_mul_right ?_ _)
      have h0 : state.cache (blk parameter data message ρ) = reference.cache (blk parameter data message ρ) := by
        exact hahead 0 (Nat.succ_pos attempts)
      rw [h0]
      cases hc : reference.cache (blk parameter data message ρ) with
      | none =>
          have hst : stOf parameter data message reference ρ = .fresh := by simp [stOf, hc]
          rw [walk_succ_fresh _ _ _ _ hst]
          simp only [Option.elim]
          exact trials_sum_le parameter gf _
      | some u0 =>
          simp only [Option.elim]
          by_cases hl : Landed parameter (blockIndex u0)
          · have hst : stOf parameter data message reference ρ = .hit := by simp [stOf, hc, hl]
            rw [walk_succ_hit _ _ _ _ hst, if_pos hl]
          · have hst : stOf parameter data message reference ρ = .miss := by simp [stOf, hc, hl]
            rw [walk_succ_miss _ _ _ _ hst, if_neg hl]

/-- The combined weight of a non-signing outcome vanishes. -/
theorem comb_none (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (s' : DebtState HashInput HashOutput Coordinate) (hrel : Related parameter data message reference s') :
    freshNewWeight parameter data message reference gf ((some none, [], [], []), s') +
      outWeight parameter data message reference 0 gp ((some none, [], [], []), s') = 0 := by
  simp only [freshNewWeight, outWeight, Option.isSome_some, if_true, add_zero]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  split_ifs with hn
  · rcases hrel ρ with h | ⟨_, u, hu', hnl⟩
    · rw [h, hn]; rfl
    · simp only [hu', Option.elim, if_neg hnl]
  · rfl

/-- The combined weight of a completed assembly is the weight of its own pair. -/
theorem comb_fin (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ)
    (hoff : RelatedOff parameter data message reference s' ρ) (hs0 : s'.cache (blk parameter data message ρ) = some u0)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')) :
    freshNewWeight parameter data message reference gf ((out.1.1, [], [], []), out.2) +
      outWeight parameter data message reference 0 gp ((out.1.1, [], [], []), out.2) ≤
      (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
        (pairWeight parameter data message reference gf gp ρ) else 0) := by
  have hkeep := finish_keeps_msg tg initial model parameter data message hparse ρ b s' u0 hs0 out hout
  have hk : ∀ ρ', out.2.cache (blk parameter data message ρ') = s'.cache (blk parameter data message ρ') :=
    fun ρ' => hkeep _ (msgInput_digestInput parameter data.root message ρ')
  by_cases hsome : out.1.1.isSome
  · rw [if_pos hsome, hk ρ, hs0]
    simp only [Option.elim]
    have hfresh : freshNewWeight parameter data message reference gf ((out.1.1, [], [], []), out.2) =
        if reference.cache (blk parameter data message ρ) = none then
          (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0) else 0 := by
      simp only [freshNewWeight, if_pos hsome]
      rw [Finset.sum_eq_single ρ]
      · simp only [hk ρ, hs0, Option.elim]
      · intro ρ' _ hne
        split_ifs with hn
        · rcases hoff ρ' hne with h | ⟨_, u, hu', hnl⟩
          · rw [hk ρ', h, hn]; rfl
          · simp only [hk ρ', hu', Option.elim, if_neg hnl]
        · rfl
      · intro h; exact absurd (Finset.mem_univ ρ) h
    rw [hfresh]
    have hout' : outWeight parameter data message reference 0 gp ((out.1.1, [], [], []), out.2) ≤
        if reference.cache (blk parameter data message ρ) = none then 0 else gp ρ (viewOf u0) := by
      have := outWeight_finish_le tg initial model parameter data message reference 0 gp ρ b s' out hout
      simp only [if_pos hsome, hk ρ, hs0, Option.elim, pairWeight] at this
      refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_))
      · rfl
      · split_ifs <;> rfl
    refine le_trans (add_le_add_right hout' _) (le_of_eq ?_)
    simp only [pairWeight]
    split_ifs <;> simp
  · rw [if_neg hsome]
    simp only [freshNewWeight, if_neg hsome, zero_add]
    unfold outWeight
    cases hr : out.1.1 with
    | none => rfl
    | some r => simp [hr] at hsome

/-- **The scan from a start, with the fresh pair it completes, weighted.** -/
theorem loop_bound_combSW
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data message ρ) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      (∀ i, i < attempts → state.cache (blk parameter data message ((nextRand ^ i) ρ)) =
        reference.cache (blk parameter data message ((nextRand ^ i) ρ))) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts ρ) budget state] *
          (weight tg initial out.2 * (freshNewWeight parameter data message reference gf out +
            outWeight parameter data message reference 0 gp out)) ≤
        weight tg initial state * walk nextRand ForestPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ :=
  loop_boundSW tg initial model parameter data message hparse hkind reference gf gp
    (fun r s' => freshNewWeight parameter data message reference gf ((r, [], [], []), s') +
      outWeight parameter data message reference 0 gp ((r, [], [], []), s'))
    (fun _ => by simp [freshNewWeight, outWeight]) (comb_none parameter data message reference gf gp)
    (fun ρ s' u0 b hoff hs0 out hout => comb_fin tg initial model parameter data message hparse reference gf gp
      ρ s' u0 b hoff hs0 out hout)

end LoopSW

end Sphincs.Security.GraphView
