import Sphincs.BridgeScan

/-! **The scan signer for weights of the reveals of every run.** The walk bound of the scan
(`scan_boundW`) for a weight of the reveal list rather than of the result: aborted runs count too,
and the weight of a run of the final assembly is bounded by the weight of its pair whatever the
run does after the digest call. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.GraphView

open SphincsFors.Security
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForestSigner Sphincs.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section LoopV

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- **One trial of the scan**, with any continuation. -/
theorem trial_boundV
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : List Coordinate → ℝ≥0∞)
    (hV0 : V [] = 0)
    (hVfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      Landed parameter (blockIndex u0) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.2.1 ≤ pairWeight parameter data message reference gf gp ρ u0)
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (cont : OracleComp CostSpec (Option Signature))
    (hih : ∀ s', Related parameter data message reference s' →
      (∀ x, x ≠ blk parameter data message ρ → s'.cache x = state.cache x) → ∀ b,
        ∑' out, Pr[= out | interp tg initial model cont b s'] * V out.1.2.1 ≤ bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        V out.1.2.1 ≤
      (state.cache (blk parameter data message ρ)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then gf (viewOf u0) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      Landed parameter (blockIndex u0) →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          V out.1.2.1 ≤
        pairWeight parameter data message reference gf gp ρ u0 := by
    intro s' u0 b hrel' hs' hl
    calc _ ≤ ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          pairWeight parameter data message reference gf gp ρ u0 := by
          refine ENNReal.tsum_le_tsum fun out => ?_
          by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
          · exact mul_le_mul_right (hVfin s' u0 b hrel' hs' hl out hout) _
          · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
      _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one
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
          refine le_trans (hfinish state u0 _ (fun ρ' _ => hrel ρ') hc hl) (le_of_eq ?_)
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
        refine ENNReal.tsum_le_tsum fun u0 => mul_le_mul_right ?_ _
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          refine le_trans (hfinish _ u0 _ (fun ρ' hρ' => by
              rw [show (state.store (blk parameter data message ρ) u0).cache (blk parameter data message ρ') =
                state.cache (blk parameter data message ρ') from
                store_cache_ne state _ _ (blk_ne_of_ne parameter data message hρ') u0]
              exact hrel ρ')
            (by simp [DebtState.store]) hl) (le_of_eq ?_)
          simp only [pairWeight, href, if_true, if_pos hl]
        · rw [if_neg hl, if_neg hl]
          exact hih _ (related_store parameter data message reference state hrel ρ hc u0 hl)
            (fun x hx => store_cache_ne state _ x hx u0) _
  · rw [tsum_probOutput_pure_mul]
    change V [] ≤ _
    rw [hV0]
    exact zero_le

/-- **The scan from a start, for any reveal weight of all runs.** The weight of the reveals of the
call, completed or not, is at most the walk value over the reference cache: a cached landed pair
pays its pool value, a fresh pair that lands pays the fresh average. The state may differ from the
reference by rejected blocks behind the start. -/
theorem loop_boundV
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : List Coordinate → ℝ≥0∞)
    (hV0 : V [] = 0)
    (hVfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      Landed parameter (blockIndex u0) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.2.1 ≤ pairWeight parameter data message reference gf gp ρ u0) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      (∀ i, i < attempts → state.cache (blk parameter data message ((nextRand ^ i) ρ)) =
        reference.cache (blk parameter data message ((nextRand ^ i) ρ))) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts ρ) budget state] *
          V out.1.2.1 ≤
        walk nextRand ForestPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ := by
  intro attempts
  induction attempts with
  | zero =>
      intro _ budget state ρ hrel _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] * V out.1.2.1 ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change V [] ≤ _
      rw [hV0]
      exact bot_le
  | succ attempts ih =>
      intro hA budget state ρ hrel hahead
      rw [signCostSourceLoop_succ]
      have hnext : ∀ s', Related parameter data message reference s' →
          (∀ x, x ≠ blk parameter data message ρ → s'.cache x = state.cache x) → ∀ b,
          ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts (nextRand ρ)) b s'] *
            V out.1.2.1 ≤
          walk nextRand ForestPrice.landing (stOf parameter data message reference)
            (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts
            (nextRand ρ) := by
        intro s' hrel' hsame b
        refine ih (Nat.le_of_succ_le hA) b s' (nextRand ρ) hrel' fun i hi => ?_
        have hpow : (nextRand ^ i) (nextRand ρ) = (nextRand ^ (i + 1)) ρ := by
          rw [pow_succ, Equiv.Perm.mul_apply]
        rw [hpow, hsame _ (blk_ne_of_ne parameter data message
          (nextRand_pow_ne ρ (i + 1) (Nat.succ_pos i) (by omega)))]
        exact hahead (i + 1) (Nat.succ_lt_succ hi)
      refine le_trans (trial_boundV tg initial model parameter data message hparse reference ρ gf gp V hV0
        (hVfin ρ) _ state hrel _ hnext budget) ?_
      have h0 : state.cache (blk parameter data message ρ) = reference.cache (blk parameter data message ρ) := by
        exact hahead 0 (Nat.succ_pos attempts)
      rw [h0]
      cases hc : reference.cache (blk parameter data message ρ) with
      | none =>
          have hst : stOf parameter data message reference ρ = .fresh := by simp [stOf, hc]
          rw [walk_succ_fresh _ _ _ _ hst]
          simp only [Option.elim]
          set bound := walk nextRand ForestPrice.landing (stOf parameter data message reference)
            (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts
            (nextRand ρ)
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
      | some u0 =>
          simp only [Option.elim]
          by_cases hl : Landed parameter (blockIndex u0)
          · have hst : stOf parameter data message reference ρ = .hit := by simp [stOf, hc, hl]
            rw [walk_succ_hit _ _ _ _ hst, if_pos hl]
          · have hst : stOf parameter data message reference ρ = .miss := by simp [stOf, hc, hl]
            rw [walk_succ_miss _ _ _ _ hst, if_neg hl]

end LoopV

end Sphincs.Security.GraphView
