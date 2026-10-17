import Sphincs.BridgeSignerPost
import Sphincs.GroupFuture

/-! The scan signer `R = R0 + i` in the interpreted lazy run: from a start, the weight of the signed
pair is at most the walk value of `LoopWalk` over the digest cache of the message (cached landed
pairs are hits, cached rejected ones are misses, the others are fresh and land with probability
`landing`). Averaged over the uniform start this is the selection law of the scan signer. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.GraphView

open SphincsFors.Security
open Concrete HiddenCost HiddenDebt HiddenGraph ForestSigner Sphincs.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The successor of a randomizer. -/
def nextRand : Equiv.Perm Randomness := Equiv.addRight 1

theorem nextRand_apply (ρ : Randomness) : nextRand ρ = ρ + 1 := rfl

theorem nextRand_pow (j : ℕ) (ρ : Randomness) : (nextRand ^ j) ρ = ρ + (j : Randomness) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, nextRand_apply]
      push_cast
      ring

/-- The scan does not return to a randomizer within `2^128` steps. -/
theorem nextRand_pow_ne (ρ : Randomness) (j : ℕ) (h0 : 0 < j) (hj : j < 2 ^ 128) : (nextRand ^ j) ρ ≠ ρ := by
  rw [nextRand_pow]
  intro h
  have h1 : (j : Randomness) = 0 := add_left_cancel (a := ρ) (h.trans (add_zero ρ).symm)
  have h2 := congrArg BitVec.toNat h1
  rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat] at h2
  have h3 : j % 2 ^ digestBits = j := Nat.mod_eq_of_lt (by simpa [digestBits] using hj)
  rw [h3] at h2
  simp at h2
  omega

variable [Params]

theorem signCostSourceLoop_succ (parameter : PublicParameter) (data : PublicData) (message : Message)
    (attempts : ℕ) (randomness : Randomness) :
    signCostSourceLoop parameter data message (attempts + 1) randomness =
      liftM (CostSpec.query (.inl (.inr (.inl
        (Security.digestInput parameter data.root message randomness))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message randomness
          else signCostSourceLoop parameter data message attempts (nextRand randomness) := by
  rw [signCostSourceLoop]
  rfl

section Scan

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- The status of the randomizers of the message in a state. -/
noncomputable def stOf (s : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) : St :=
  (s.cache (blk parameter data message ρ)).elim .fresh fun u0 =>
    if Landed parameter (blockIndex u0) then .hit else .miss

/-- **One trial of the scan**, with any continuation. -/
theorem trial_boundS
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (W : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hWabort : ∀ s', W none s' = 0)
    (hWfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        W out.1.1 out.2 ≤ (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0))
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (cont : OracleComp CostSpec (Option Signature))
    (hih : ∀ s', Related parameter data message reference s' →
      (∀ x, x ≠ blk parameter data message ρ → s'.cache x = state.cache x) → ∀ b,
        ∑' out, Pr[= out | interp tg initial model cont b s'] * W out.1.1 out.2 ≤ bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        W out.1.1 out.2 ≤
      (state.cache (blk parameter data message ρ)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then gf (viewOf u0) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          W out.1.1 out.2 ≤
        pairWeight parameter data message reference gf gp ρ u0 := by
    intro s' u0 b hrel' hs'
    refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) (finish_bound₁ tg initial model parameter data message ρ
      (hparse ρ) s' u0 hs' _ b)
    by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
    · exact mul_le_mul_right (hWfin s' u0 b hrel' hs' out hout) _
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
        refine ENNReal.tsum_le_tsum fun u0 => mul_le_mul_right ?_ _
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          refine le_trans (hfinish _ u0 _ (fun ρ' hρ' => by
              rw [show (state.store (blk parameter data message ρ) u0).cache (blk parameter data message ρ') =
                state.cache (blk parameter data message ρ') from
                store_cache_ne state _ _ (blk_ne_of_ne parameter data message hρ') u0]
              exact hrel ρ')
            (by simp [DebtState.store])) (le_of_eq ?_)
          simp only [pairWeight, href, if_true, if_pos hl]
        · rw [if_neg hl, if_neg hl]
          exact hih _ (related_store parameter data message reference state hrel ρ hc u0 hl)
            (fun x hx => store_cache_ne state _ x hx u0) _
  · rw [tsum_probOutput_pure_mul]
    rw [hWabort]
    exact zero_le

/-- **The scan from a start.** The weight of the signed pair is at most the walk value over the
reference cache: a cached landed pair pays its pool value, a fresh pair that lands pays the fresh
average. The state may differ from the reference by rejected blocks behind the start. -/
theorem scan_boundW
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (W : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hWabort : ∀ s', W none s' = 0)
    (hWnone : ∀ s' : DebtState HashInput HashOutput Coordinate, Related parameter data message reference s' →
      W (some none) s' = 0)
    (hWfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        W out.1.1 out.2 ≤ (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0)) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      (∀ i, i < attempts → state.cache (blk parameter data message ((nextRand ^ i) ρ)) =
        reference.cache (blk parameter data message ((nextRand ^ i) ρ))) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts ρ) budget state] *
          W out.1.1 out.2 ≤
        walk nextRand ForestPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ := by
  intro attempts
  induction attempts with
  | zero =>
      intro _ budget state ρ hrel _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] * W out.1.1 out.2 ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change W (some none) state ≤ _
      rw [hWnone state hrel]
      exact bot_le
  | succ attempts ih =>
      intro hA budget state ρ hrel hahead
      rw [signCostSourceLoop_succ]
      have hnext : ∀ s', Related parameter data message reference s' →
          (∀ x, x ≠ blk parameter data message ρ → s'.cache x = state.cache x) → ∀ b,
          ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts (nextRand ρ)) b s'] *
            W out.1.1 out.2 ≤
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
      refine le_trans (trial_boundS tg initial model parameter data message hparse reference ρ gf gp W hWabort
        (hWfin ρ) _ state hrel _ hnext budget) ?_
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

end Scan

section Post

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- **The scan, support.** -/
theorem scan_post (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ ρ digest budget (s1 : DebtState HashInput HashOutput Coordinate), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data message ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail) :
    ∀ attempts budget (s : DebtState HashInput HashOutput Coordinate) (ρ : Randomness), Prepared initial s →
      ∀ out ∈ support (interp tg initial model (signCostSourceLoop parameter data message attempts ρ) budget s),
        ∀ r, out.1.1 = some r → SignPost parameter data message Fail s out.2 out.1.2.1 r := by
  intro attempts
  induction attempts with
  | zero =>
      intro budget s ρ _ out hout r hr
      change out ∈ support (interp tg initial model (pure none) budget s) at hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      cases hr
      exact Or.inl ⟨rfl, rfl, fun ρ => RelatedAt.refl parameter data message s ρ⟩
  | succ attempts ih =>
      intro budget s ρ hprep out hout r hr
      rw [signCostSourceLoop_succ, interp_ordinary] at hout
      split_ifs at hout with h1
      · rw [ordinaryStep, hparse ρ] at hout
        simp only at hout
        rw [support_bind] at hout
        obtain ⟨res, hres, hout⟩ := Set.mem_iUnion₂.1 hout
        rw [support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        simp only at hr ⊢
        have hstep : res.2.cache (blk parameter data message ρ) = some res.1 ∧
            (s.cache (blk parameter data message ρ) = none ∨
              s.cache (blk parameter data message ρ) = some res.1) ∧
            (∀ x, x ≠ blk parameter data message ρ → res.2.cache x = s.cache x) ∧
            Prepared initial res.2 := by
          cases hc0 : s.cache (blk parameter data message ρ) with
          | some u =>
              rw [readOutside_cached _ s u hc0, support_pure, Set.mem_singleton_iff] at hres
              rw [hres]
              exact ⟨hc0, Or.inr rfl, fun _ _ => rfl, hprep⟩
          | none =>
              rw [readOutside_fresh _ s hc0, support_map] at hres
              obtain ⟨u, _, rfl⟩ := hres
              exact ⟨by simp [DebtState.store], Or.inl rfl, fun x hx => store_cache_ne s _ x hx u,
                prepared_store initial s hprep _ u hc0⟩
        obtain ⟨hb0, hb0s, hrest, hprep1⟩ := hstep
        by_cases hl : Landed parameter (blockIndex res.1)
        · rw [if_pos hl] at ho
          obtain ⟨hf0, hfother, hfrev, hfsig, hffail⟩ :=
            finish_post tg initial model parameter data message hparse Fail hfail ρ _ res.2 hprep1 res.1 hb0 o ho r hr
          refine Or.inr ⟨ρ, res.1, ⟨hf0, hl, hb0s, fun ρ' hρ' => ?_⟩, hfrev, hfsig, fun hn => ?_⟩
          · refine Or.inl ?_
            rw [hfother _ (msgInput_digestInput parameter data.root message ρ'),
              hrest _ (blk_ne_of_ne parameter data message hρ')]
          · obtain ⟨hrv, hfl⟩ := hffail hn
            exact ⟨hrv, fun _ => hfl⟩
        · rw [if_neg hl] at ho
          have hrel1 : ∀ ρ', RelatedAt parameter data message s res.2 ρ' := by
            intro ρ'
            by_cases hρ : ρ' = ρ
            · subst hρ
              rcases hb0s with hn | hs
              · exact Or.inr ⟨hn, res.1, hb0, hl⟩
              · exact Or.inl (hb0.trans hs.symm)
            · exact Or.inl (hrest _ (blk_ne_of_ne parameter data message hρ))
          rcases ih _ res.2 (nextRand ρ) hprep1 o ho r hr with ⟨hrn, hrv, hrel⟩ | ⟨ρs, u0, hsel, hrev, hsig, hfl⟩
          · exact Or.inl ⟨hrn, hrv, fun ρ' => (hrel1 ρ').trans parameter data message (hrel ρ')⟩
          · obtain ⟨hs0, hland, hs0r, hothers⟩ := hsel
            have hr1 := hrel1 ρs
            refine Or.inr ⟨ρs, u0, ⟨hs0, hland, ?_, fun ρ' hρ' =>
              (hrel1 ρ').trans parameter data message (hothers ρ' hρ')⟩, hrev, hsig, fun hn => ?_⟩
            · rcases hr1 with he | ⟨hn', _⟩
              · rw [← he]; exact hs0r
              · exact Or.inl hn'
            · obtain ⟨hrv, hfl'⟩ := hfl hn
              refine ⟨hrv, fun hnone => hfl' ?_⟩
              rcases hr1 with he | ⟨_, u, hu, hnl⟩
              · rw [he]; exact hnone
              · rcases hs0r with h | h
                · exact h
                · rw [hu] at h
                  cases h
                  exact absurd hland hnl
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hr
        cases hr

/-- **The scan signer, support.** -/
theorem source_post (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ ρ digest budget (s1 : DebtState HashInput HashOutput Coordinate), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data message ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (budget : ℕ) (s : DebtState HashInput HashOutput Coordinate) (hprep : Prepared initial s) :
    ∀ out ∈ support (interp tg initial model (signCostSource parameter data message) budget s),
      ∀ r, out.1.1 = some r → SignPost parameter data message Fail s out.2 out.1.2.1 r := by
  intro out hout r hr
  unfold signCostSource at hout
  rw [interp_liftProb_bind, support_bind] at hout
  obtain ⟨ρ, _, hout⟩ := Set.mem_iUnion₂.1 hout
  exact scan_post tg initial model parameter data message hparse Fail hfail _ budget s ρ hprep out hout r hr

/-- The scan only queries message inputs of the signed message. -/
theorem avoids_scan :
    ∀ attempts ρ, Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate)
      (fun x => IsMsgInput x ∧ ∀ ρ, x ≠ blk parameter data message ρ)
      (signCostSourceLoop parameter data message attempts ρ) := by
  intro attempts
  induction attempts with
  | zero => intro ρ; exact avoids_pure _ _
  | succ attempts ih =>
      intro ρ
      rw [signCostSourceLoop_succ]
      refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun first => ?_⟩
      · cases hb
        exact hx.2 ρ rfl
      · split_ifs
        · rw [finishCostSource_eq]
          refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun a => ?_⟩
          · cases hb
            exact hx.2 ρ rfl
          exact avoids_mono (fun x hx => hx.1) (avoids_finishRest parameter data message ρ _)
        · exact ih _

theorem avoids_source :
    Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate)
      (fun x => IsMsgInput x ∧ ∀ ρ, x ≠ blk parameter data message ρ)
      (signCostSource parameter data message) :=
  avoids_bind _ (avoids_liftProb _ _) fun ρ => avoids_scan parameter data message _ ρ

end Post

end Sphincs.Security.GraphView
