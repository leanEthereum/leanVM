import FORS.ScanSigner.Scan

/-! **The scan signer for weights of the reveals of every run.** The walk bound of the scan
(`scan_boundW`) for a weight of the reveal list rather than of the result: aborted runs count too,
and the weight of a run of the final assembly is bounded by the weight of its pair whatever the
run does after the digest call. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.GraphView

variable [Params]

open FORS.Base
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForsSigner FORS.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable


section LoopV

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- **One trial of the scan**, with any continuation. The trial reads the index block alone, so a
fresh pair is only drawn whole by the final assembly that follows it (`interp_presample_new`). -/
theorem trial_boundV
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : List Coordinate → ℝ≥0∞)
    (hV0 : V [] = 0)
    (hVfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      Landed parameter (blockIndex (u firstCall)) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.2.1 ≤ pairWeight parameter data message reference gf gp ρ u)
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state)
    (hinv : PairInv parameter data message state)
    (hpair : ∀ call, state.cache (pblk parameter data message ρ call) =
      reference.cache (pblk parameter data message ρ call))
    (cont : OracleComp CostSpec (Option Signature))
    (hih : ∀ s', Related parameter data message reference s' → PairInv parameter data message s' →
      (∀ x, (∀ call, x ≠ pblk parameter data message ρ call) → s'.cache x = state.cache x) → ∀ b,
        ∑' out, Pr[= out | interp tg initial model cont b s'] * V out.1.2.1 ≤ bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        V out.1.2.1 ≤
      (state.cache (blk parameter data message ρ)).elim
        (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
          (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      Landed parameter (blockIndex (u firstCall)) →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          V out.1.2.1 ≤
        pairWeight parameter data message reference gf gp ρ u := by
    intro s' u b hrel' hs' hl
    calc _ ≤ ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          pairWeight parameter data message reference gf gp ρ u := by
          refine ENNReal.tsum_le_tsum fun out => ?_
          by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
          · exact mul_le_mul_right (hVfin s' u b hrel' hs' hl out hout) _
          · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
      _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ firstCall]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          obtain ⟨u, hu, hucall⟩ :=
            pcache_of_isSome parameter data message state ρ ((hinv ρ).2 u0 hc hl)
          have hu0 : u firstCall = u0 := Option.some_inj.1 ((hucall firstCall).symm.trans hc)
          have href : reference.cache (blk parameter data message ρ) = some u0 := by
            rw [← hpair firstCall]; exact hc
          have hpcsame : pcache parameter data message reference ρ =
              pcache parameter data message state ρ := by
            unfold pcache
            exact congrArg _ (funext fun call => (hpair call).symm)
          have hpv : poolValue parameter data message reference gp ρ = gp ρ (viewOf u) := by
            unfold poolValue
            rw [hpcsame.trans hu]
            simp only [Option.elim, hu0]
            rw [if_pos hl]
          have hpw : pairWeight parameter data message reference gf gp ρ u = gp ρ (viewOf u) := by
            unfold pairWeight
            rw [if_neg (by rw [href]; simp)]
          rw [hpv, ← hpw]
          exact hfinish state u _ (fun ρ' _ => hrel ρ') hucall (by rw [hu0]; exact hl)
        · rw [if_neg hl, if_neg hl]
          exact hih state hrel hinv (fun _ _ => rfl) _
    | none =>
        have hfresh : ∀ call, state.cache (pblk parameter data message ρ call) = none := (hinv ρ).1 hc
        have href : reference.cache (blk parameter data message ρ) = none := by
          rw [← hpair firstCall]; exact hc
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        refine le_trans (interp_presample_new tg initial model (pblk parameter data message ρ)
          (pblk_injective parameter data message ρ) (hkind ρ) firstCall
          (fun first => if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
            else cont) (budget - 1) state hfresh (fun out => V out.1.2.1)
          (fun _ _ _ _ => le_rfl)) ?_
        rw [tsum_uniform_eq]
        have hcard : (Fintype.card (DigestCall → HashOutput) : ℝ≥0∞) =
            (Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls := by
          rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        rw [hcard]
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun u _ => ?_)
        by_cases hl : Landed parameter (blockIndex (u firstCall))
        · rw [if_pos hl, if_pos hl]
          have hall : ∀ call, (storeAll (pblk parameter data message ρ) u state).cache
              (pblk parameter data message ρ call) = some (u call) :=
            fun call => storeAll_cache_self _ (pblk_injective parameter data message ρ) u state call
          have hpw : pairWeight parameter data message reference gf gp ρ u = gf (viewOf u) := by
            unfold pairWeight
            rw [if_pos href, if_pos hl]
          rw [← hpw]
          exact hfinish _ u _ (relatedOff_storeAll parameter data message reference state hrel ρ u) hall hl
        · rw [if_neg hl, if_neg hl]
          exact hih _ (related_storeAll parameter data message reference state hrel ρ hc u hl)
            (pairInv_storeAll parameter data message state hinv ρ u hl)
            (fun x hx => storeAll_cache_other _ _ _ _ fun call => Ne.symm (hx call)) _
  · rw [tsum_probOutput_pure_mul]
    change V [] ≤ _
    rw [hV0]
    exact zero_le

/-- **The scan from a start, for any reveal weight of all runs.** The weight of the reveals of the
call, completed or not, is at most the walk value over the reference cache: a cached landed pair
pays its pool value, a fresh pair that lands pays the fresh average. The state may differ from the
reference by rejected blocks behind the start. -/
theorem loop_boundV
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : List Coordinate → ℝ≥0∞)
    (hV0 : V [] = 0)
    (hVfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate)
      (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      Landed parameter (blockIndex (u firstCall)) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.2.1 ≤ pairWeight parameter data message reference gf gp ρ u) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      PairInv parameter data message state →
      (∀ i, i < attempts → ∀ call,
        state.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call) =
        reference.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call)) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget state] *
          V out.1.2.1 ≤
        walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ := by
  intro attempts
  induction attempts with
  | zero =>
      intro _ budget state ρ hrel _ _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] * V out.1.2.1 ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change V [] ≤ _
      rw [hV0]
      exact bot_le
  | succ attempts ih =>
      intro hA budget state ρ hrel hinv hahead
      rw [signCostSourceLoop_succ]
      have hnext : ∀ s', Related parameter data message reference s' → PairInv parameter data message s' →
          (∀ x, (∀ call, x ≠ pblk parameter data message ρ call) → s'.cache x = state.cache x) → ∀ b,
          ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts (nextRand (data.steps message) ρ)) b s'] *
            V out.1.2.1 ≤
          walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
            (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts
            (nextRand (data.steps message) ρ) := by
        intro s' hrel' hinv' hsame b
        refine ih (Nat.le_of_succ_le hA) b s' (nextRand (data.steps message) ρ) hrel' hinv' fun i hi call => ?_
        have hpow : (nextRand (data.steps message) ^ i) (nextRand (data.steps message) ρ) = (nextRand (data.steps message) ^ (i + 1)) ρ := by
          rw [pow_succ, Equiv.Perm.mul_apply]
        rw [hpow, hsame _ fun call' => pblk_ne_of_ne parameter data message
          (nextRand_pow_ne (data.steps message) ρ (i + 1) (Nat.succ_pos i) (by omega)) call call']
        exact hahead (i + 1) (Nat.succ_lt_succ hi) call
      refine le_trans (trial_boundV tg initial model parameter data message hparse hkind reference ρ gf gp V hV0
        (hVfin ρ) _ state hrel hinv (hahead 0 (Nat.succ_pos attempts)) _ hnext budget) ?_
      have h0 : state.cache (blk parameter data message ρ) = reference.cache (blk parameter data message ρ) :=
        hahead 0 (Nat.succ_pos attempts) firstCall
      rw [h0]
      cases hc : reference.cache (blk parameter data message ρ) with
      | none =>
          have hst : stOf parameter data message reference ρ = .fresh := by simp [stOf, hc]
          rw [walk_succ_fresh _ _ _ _ hst]
          simp only [Option.elim]
          set bound := walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
            (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts
            (nextRand (data.steps message) ρ)
          have hsplit : (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
              (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound)) =
              (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
                (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else 0)) +
              bound * ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
                (if Landed parameter (blockIndex (u firstCall)) then 0 else 1) := by
            rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
            refine tsum_congr fun u => ?_
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

end FORS.Security.GraphView
