import FORS.ScanSigner.AfterSigning
import FORS.ScanSigner.Group
import FORS.CoverPotential.Presample

/-! The scan signer `R = R0 + i δ` in the interpreted lazy run: from a start, the weight of the signed
pair is at most the walk value of `LoopWalk` over the digest cache of the message (cached landed
pairs are hits, cached rejected ones are misses, the others are fresh and land with probability
`landing`). Averaged over the uniform start this is the selection law of the scan signer. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.GraphView

variable [Params]

open FORS.Base
open Concrete HiddenCost HiddenDebt HiddenGraph ForsSigner FORS.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The successor of a randomizer in a walk whose step is `walkStep half`. -/
def nextRand (half : Randomness) : Equiv.Perm Randomness := Equiv.addRight (walkStep half)

theorem nextRand_apply (half ρ : Randomness) : nextRand half ρ = ρ + walkStep half := rfl

theorem nextRand_pow (half : Randomness) (j : ℕ) (ρ : Randomness) :
    (nextRand half ^ j) ρ = ρ + (j : Randomness) * walkStep half := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, nextRand_apply]
      push_cast
      ring

/-- The scan does not return to a randomizer within `2^128` steps. -/
theorem nextRand_pow_ne (half ρ : Randomness) (j : ℕ) (h0 : 0 < j) (hj : j < 2 ^ 128) :
    (nextRand half ^ j) ρ ≠ ρ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h := walk_iterate_ne half ρ i hj
  rwa [walk_iterate, show ρ + walkStep half + (i : Randomness) * walkStep half =
    ρ + ((i + 1 : ℕ) : Randomness) * walkStep half by push_cast; ring, ← nextRand_pow] at h


theorem signCostSourceLoop_succ (parameter : PublicParameter) (data : PublicData) (message : Message)
    (attempts : ℕ) (randomness : Randomness) :
    signCostSourceLoop parameter data message (data.step message) (attempts + 1) randomness =
      liftM (CostSpec.query (.inl (.inr (.inl
        (Security.digestInput parameter data.root message randomness firstCall))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message randomness
          else signCostSourceLoop parameter data message (data.step message) attempts (nextRand (data.steps message) randomness) := by
  rw [signCostSourceLoop]
  rfl

section Pairs

variable (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- The index block of a randomizer is the block of its first call. -/
theorem blk_eq_pblk (ρ : Randomness) :
    blk parameter data message ρ = pblk parameter data message ρ firstCall := rfl

/-- Blocks of distinct randomizers differ, whatever their calls. -/
theorem pblk_ne_of_ne {ρ ρ' : Randomness} (h : ρ ≠ ρ') (call call' : DigestCall) :
    pblk parameter data message ρ call ≠ pblk parameter data message ρ' call' := fun heq =>
  h (payload_randomness_injective data.root message (tweakableInput_injective heq).2.2)

/-- **The pair invariant of a state**: a pair whose index block is uncached is wholly uncached, and
a pair whose index block lands is wholly cached. The trial of the scan reads the index block alone,
so it preserves both: it only ever adds a rejected one. -/
def PairInv (state : DebtState HashInput HashOutput Coordinate) : Prop :=
  ∀ ρ, (state.cache (blk parameter data message ρ) = none →
      ∀ call, state.cache (pblk parameter data message ρ call) = none) ∧
    (∀ u0, state.cache (blk parameter data message ρ) = some u0 → Landed parameter (blockIndex u0) →
      ∀ call, (state.cache (pblk parameter data message ρ call)).isSome)

/-- **The first half of the pair invariant**: a pair whose index block is uncached is wholly
uncached. A signing call preserves this half whether or not it completes. -/
def PairFresh (state : DebtState HashInput HashOutput Coordinate) : Prop :=
  ∀ ρ, state.cache (blk parameter data message ρ) = none →
    ∀ call, state.cache (pblk parameter data message ρ call) = none

theorem pairFresh_of_pairInv {state : DebtState HashInput HashOutput Coordinate}
    (hinv : PairInv parameter data message state) : PairFresh parameter data message state :=
  fun ρ => (hinv ρ).1

/-- Storing a rejected index block keeps the pair invariant: its pair is no longer fresh, and it
does not land. -/
theorem pairInv_store (state : DebtState HashInput HashOutput Coordinate)
    (hinv : PairInv parameter data message state) (ρ : Randomness) (u0 : HashOutput)
    (hu : ¬Landed parameter (blockIndex u0)) :
    PairInv parameter data message (state.store (blk parameter data message ρ) u0) := by
  intro ρ'
  by_cases hρ : ρ' = ρ
  · have hfirst : (state.store (blk parameter data message ρ) u0).cache
        (blk parameter data message ρ') = some u0 := by
      rw [hρ]; simp [DebtState.store]
    refine ⟨fun h => absurd (hfirst.symm.trans h) (by simp), fun v h0 hl => ?_⟩
    rw [hfirst] at h0
    cases h0
    exact absurd hl hu
  · have hsame : ∀ call, (state.store (blk parameter data message ρ) u0).cache
        (pblk parameter data message ρ' call) = state.cache (pblk parameter data message ρ' call) :=
      fun call => store_cache_ne state _ _ (pblk_ne_of_ne parameter data message hρ call firstCall) u0
    exact ⟨fun h call => (hsame call).trans ((hinv ρ').1 ((hsame firstCall).symm.trans h) call),
      fun v h0 hl call => (hsame call) ▸ (hinv ρ').2 v ((hsame firstCall).symm.trans h0) hl call⟩

/-- A wholly cached pair has a block tuple. -/
theorem pcache_of_isSome (state : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (h : ∀ call, (state.cache (pblk parameter data message ρ call)).isSome) :
    ∃ u, pcache parameter data message state ρ = some u ∧
      ∀ call, state.cache (pblk parameter data message ρ call) = some (u call) := by
  refine ⟨fun call => (state.cache (pblk parameter data message ρ call)).get (h call), ?_,
    fun call => (Option.some_get (h call)).symm⟩
  unfold pcache
  exact allSome_of_eq _ _ fun call => (Option.some_get (h call)).symm

/-- Storing a rejected pair keeps the relation to the reference. -/
theorem related_storeAll (reference state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (ρ : Randomness)
    (hs : state.cache (blk parameter data message ρ) = none) (u : DigestCall → HashOutput)
    (hu : ¬Landed parameter (blockIndex (u firstCall))) :
    Related parameter data message reference (storeAll (pblk parameter data message ρ) u state) := by
  have href : reference.cache (blk parameter data message ρ) = none := by
    rcases hrel ρ with h | ⟨h, _⟩
    · rw [← h]; exact hs
    · exact h
  intro ρ'
  by_cases hρ : ρ' = ρ
  · subst hρ
    exact Or.inr ⟨href, u firstCall,
      storeAll_cache_self _ (pblk_injective parameter data message _) u state firstCall, hu⟩
  · have h : (storeAll (pblk parameter data message ρ) u state).cache (blk parameter data message ρ') =
        state.cache (blk parameter data message ρ') :=
      storeAll_cache_other _ _ _ _ fun call =>
        pblk_ne_of_ne parameter data message (Ne.symm hρ) call firstCall
    rw [h]
    exact hrel ρ'

/-- Storing a rejected pair keeps the pair invariant. -/
theorem pairInv_storeAll (state : DebtState HashInput HashOutput Coordinate)
    (hinv : PairInv parameter data message state) (ρ : Randomness)
    (u : DigestCall → HashOutput) (hu : ¬Landed parameter (blockIndex (u firstCall))) :
    PairInv parameter data message (storeAll (pblk parameter data message ρ) u state) := by
  intro ρ'
  by_cases hρ : ρ' = ρ
  · subst hρ
    have hfirst : (storeAll (pblk parameter data message ρ') u state).cache
        (blk parameter data message ρ') = some (u firstCall) :=
      storeAll_cache_self _ (pblk_injective parameter data message _) u state firstCall
    refine ⟨fun h => absurd (hfirst.symm.trans h) (by simp), fun u0 h0 hl => ?_⟩
    rw [hfirst] at h0
    cases h0
    exact absurd hl hu
  · have hsame : ∀ call, (storeAll (pblk parameter data message ρ) u state).cache
        (pblk parameter data message ρ' call) = state.cache (pblk parameter data message ρ' call) :=
      fun call => storeAll_cache_other _ _ _ _ fun call' =>
        pblk_ne_of_ne parameter data message (Ne.symm hρ) call' call
    exact ⟨fun h call => (hsame call).trans ((hinv ρ').1 ((hsame firstCall).symm.trans h) call),
      fun u0 h0 hl call => (hsame call) ▸ (hinv ρ').2 u0 ((hsame firstCall).symm.trans h0) hl call⟩

/-- Storing one pair leaves the others related to the reference. -/
theorem relatedOff_storeAll (reference state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (ρ : Randomness)
    (u : DigestCall → HashOutput) :
    RelatedOff parameter data message reference
      (storeAll (pblk parameter data message ρ) u state) ρ := by
  intro ρ' hρ'
  have h : (storeAll (pblk parameter data message ρ) u state).cache (blk parameter data message ρ') =
      state.cache (blk parameter data message ρ') :=
    storeAll_cache_other _ _ _ _ fun call =>
      pblk_ne_of_ne parameter data message (Ne.symm hρ') call firstCall
  rw [h]
  exact hrel ρ'

end Pairs

section Scan

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- The status of the randomizers of the message in a state. -/
noncomputable def stOf (s : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) : St :=
  (s.cache (blk parameter data message ρ)).elim .fresh fun u0 =>
    if Landed parameter (blockIndex u0) then .hit else .miss

/-- **One trial of the scan**, with any continuation. The trial reads the index block alone, so a
fresh pair is only drawn whole by the final assembly that follows it (`interp_presample_new`). -/
theorem trial_boundS
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (W : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hWabort : ∀ s', W none s' = 0)
    (hWstore : ∀ r (s' : DebtState HashInput HashOutput Coordinate) (y : HashInput) (v : HashOutput),
      s'.cache y = none → W r s' ≤ W r (s'.store y v))
    (hWfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        W out.1.1 out.2 ≤ (if out.1.1.isSome then (pcache parameter data message out.2 ρ).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0))
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state)
    (hinv : PairInv parameter data message state)
    (hpair : ∀ call, state.cache (pblk parameter data message ρ call) =
      reference.cache (pblk parameter data message ρ call))
    (cont : OracleComp CostSpec (Option Signature))
    (hih : ∀ s', Related parameter data message reference s' → PairInv parameter data message s' →
      (∀ x, (∀ call, x ≠ pblk parameter data message ρ call) → s'.cache x = state.cache x) → ∀ b,
        ∑' out, Pr[= out | interp tg initial model cont b s'] * W out.1.1 out.2 ≤ bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        W out.1.1 out.2 ≤
      (state.cache (blk parameter data message ρ)).elim
        (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
          (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          W out.1.1 out.2 ≤ pairWeight parameter data message reference gf gp ρ u := by
    intro s' u b hrel' hs'
    refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) (finish_boundAll tg initial model parameter data message ρ
      (hparse ρ) s' u hs' _ b)
    by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
    · exact mul_le_mul_right (hWfin s' u b hrel' hs' out hout) _
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
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
          exact hfinish state u _ (fun ρ' _ => hrel ρ') hucall
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
            else cont) (budget - 1) state hfresh (fun out => W out.1.1 out.2)
          (fun out y v hy => hWstore out.1.1 out.2 y v hy)) ?_
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
          exact hfinish _ u _ (relatedOff_storeAll parameter data message reference state hrel ρ u) hall
        · rw [if_neg hl, if_neg hl]
          exact hih _ (related_storeAll parameter data message reference state hrel ρ hc u hl)
            (pairInv_storeAll parameter data message state hinv ρ u hl)
            (fun x hx => storeAll_cache_other _ _ _ _ fun call => Ne.symm (hx call)) _
  · rw [tsum_probOutput_pure_mul]
    rw [hWabort]
    exact zero_le

/-- **The scan from a start.** The weight of the signed pair is at most the walk value over the
reference cache: a cached landed pair pays its pool value, a fresh pair that lands pays the fresh
average. The state may differ from the reference by rejected blocks behind the start. -/
theorem scan_boundW
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (W : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hWabort : ∀ s', W none s' = 0)
    (hWstore : ∀ r (s' : DebtState HashInput HashOutput Coordinate) (y : HashInput) (v : HashOutput),
      s'.cache y = none → W r s' ≤ W r (s'.store y v))
    (hWnone : ∀ s' : DebtState HashInput HashOutput Coordinate, Related parameter data message reference s' →
      W (some none) s' = 0)
    (hWfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate)
      (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        W out.1.1 out.2 ≤ (if out.1.1.isSome then (pcache parameter data message out.2 ρ).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0)) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      PairInv parameter data message state →
      (∀ i, i < attempts → ∀ call,
        state.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call) =
        reference.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call)) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget state] *
          W out.1.1 out.2 ≤
        walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ := by
  intro attempts
  induction attempts with
  | zero =>
      intro _ budget state ρ hrel _ _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] * W out.1.1 out.2 ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change W (some none) state ≤ _
      rw [hWnone state hrel]
      exact bot_le
  | succ attempts ih =>
      intro hA budget state ρ hrel hinv hahead
      rw [signCostSourceLoop_succ]
      have hnext : ∀ s', Related parameter data message reference s' → PairInv parameter data message s' →
          (∀ x, (∀ call, x ≠ pblk parameter data message ρ call) → s'.cache x = state.cache x) → ∀ b,
          ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts (nextRand (data.steps message) ρ)) b s'] *
            W out.1.1 out.2 ≤
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
      refine le_trans (trial_boundS tg initial model parameter data message hparse hkind reference ρ gf gp W hWabort
        hWstore (hWfin ρ) _ state hrel hinv (hahead 0 (Nat.succ_pos attempts)) _ hnext budget) ?_
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

end Scan

section Post

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- **The scan, support.** -/
theorem scan_post (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ ρ digest budget (s1 : DebtState HashInput HashOutput Coordinate), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data message ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail) :
    ∀ attempts budget (s : DebtState HashInput HashOutput Coordinate) (ρ : Randomness), Prepared initial s →
      ∀ out ∈ support (interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget s),
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
      · rw [ordinaryStep, hparse ρ firstCall] at hout
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
          obtain ⟨u, hu0s, hpc, hfother, hfrev, hfsig, hffail⟩ :=
            finish_post tg initial model parameter data message hparse Fail hfail ρ _ res.2 hprep1 o ho r hr
          have hufirst : u firstCall = res.1 := by
            rcases hu0s firstCall with h | h
            · exact absurd (hb0.symm.trans h) (by simp)
            · exact Option.some_inj.1 (h.symm.trans hb0)
          refine Or.inr ⟨ρ, u, ⟨hpc, by rw [hufirst]; exact hl, by rw [hufirst]; exact hb0s,
            fun ρ' hρ' => ?_⟩, hfrev, hfsig, fun hn => ?_⟩
          · exact Or.inl ((hfother _ (msgInput_digestInput parameter data.root message ρ' firstCall)
              (fun call => pblk_ne_of_ne parameter data message hρ' firstCall call)).trans
              (hrest _ (blk_ne_of_ne parameter data message hρ')))
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
          rcases ih _ res.2 (nextRand (data.steps message) ρ) hprep1 o ho r hr with ⟨hrn, hrv, hrel⟩ | ⟨ρs, u, hsel, hrev, hsig, hfl⟩
          · exact Or.inl ⟨hrn, hrv, fun ρ' => (hrel1 ρ').trans parameter data message (hrel ρ')⟩
          · obtain ⟨hs0, hland, hs0r, hothers⟩ := hsel
            have hr1 := hrel1 ρs
            refine Or.inr ⟨ρs, u, ⟨hs0, hland, ?_, fun ρ' hρ' =>
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
theorem source_post (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
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

/-- A completed final assembly holds every block of the pair it signed: its digest call reads
them all, and the run only grows the cache. -/
theorem finish_pcache (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (ρ : Randomness) (budget : ℕ) (s' : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget s'))
    (hsome : out.1.1 ≠ none) (call : DigestCall) :
    (out.2.cache (pblk parameter data message ρ call)).isSome := by
  rw [finishCostSource_eq] at hout
  obtain ⟨u, b, s2, o, _, hs2, _, _, ho, _, _, hst⟩ :=
    all_read_support tg initial model _ (pblk_injective parameter data message ρ) (hparse ρ) s'
      _ budget out hout hsome
  rw [hst, (interp_extends tg initial model _ b s2 o ho).1 _ _ (hs2 call)]
  rfl

/-- **The scan keeps fresh pairs whole**, whether or not it completes: a trial caches the index
block of its own pair alone, and the final assembly reads only the pair it signs. -/
theorem scan_pairFresh (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none) :
    ∀ attempts budget (s : DebtState HashInput HashOutput Coordinate) (ρ : Randomness),
      PairFresh parameter data message s →
      ∀ out ∈ support (interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget s),
        PairFresh parameter data message out.2 := by
  intro attempts
  induction attempts with
  | zero =>
      intro budget s ρ hfresh out hout
      change out ∈ support (interp tg initial model (pure none) budget s) at hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout]
      exact hfresh
  | succ attempts ih =>
      intro budget s ρ hfresh out hout
      rw [signCostSourceLoop_succ, interp_ordinary] at hout
      split_ifs at hout with h1
      · rw [ordinaryStep, hparse ρ firstCall] at hout
        simp only at hout
        rw [support_bind] at hout
        obtain ⟨res, hres, hout⟩ := Set.mem_iUnion₂.1 hout
        rw [support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        show PairFresh parameter data message o.2
        have hstep : res.2.cache (blk parameter data message ρ) = some res.1 ∧
            (∀ x, x ≠ blk parameter data message ρ → res.2.cache x = s.cache x) := by
          cases hc0 : s.cache (blk parameter data message ρ) with
          | some v =>
              rw [readOutside_cached _ s v hc0, support_pure, Set.mem_singleton_iff] at hres
              rw [hres]
              exact ⟨hc0, fun _ _ => rfl⟩
          | none =>
              rw [readOutside_fresh _ s hc0, support_map] at hres
              obtain ⟨v, _, rfl⟩ := hres
              exact ⟨by simp [DebtState.store], fun x hx => store_cache_ne s _ x hx v⟩
        obtain ⟨hb0, hrest⟩ := hstep
        have hfresh1 : PairFresh parameter data message res.2 := by
          intro ρ' hρ' call
          by_cases hρ : ρ' = ρ
          · exact absurd hρ' (by rw [hρ, hb0]; simp)
          · exact (hrest _ (pblk_ne_of_ne parameter data message hρ call firstCall)).trans
              (hfresh ρ' ((hrest _ (blk_ne_of_ne parameter data message hρ)).symm.trans hρ') call)
        by_cases hl : Landed parameter (blockIndex res.1)
        · rw [if_pos hl] at ho
          have hkeep := finish_keeps_msg tg initial model parameter data message ρ (budget - 1) res.2 o ho
          intro ρ' hρ' call
          by_cases hρ : ρ' = ρ
          · rw [hρ] at hρ'
            exact absurd (((interp_extends tg initial model _ (budget - 1) res.2 o ho).1 _ _ hb0).symm.trans hρ')
              (by simp)
          · have hcall : ∀ c, o.2.cache (pblk parameter data message ρ' c) =
                res.2.cache (pblk parameter data message ρ' c) := fun c =>
              hkeep _ (msgInput_digestInput parameter data.root message ρ' c)
                fun c' => pblk_ne_of_ne parameter data message hρ c c'
            exact (hcall call).trans (hfresh1 ρ' ((hcall firstCall).symm.trans hρ') call)
        · rw [if_neg hl] at ho
          exact ih _ res.2 _ hfresh1 o ho
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout]
        exact hfresh

/-- **The scan keeps the pair invariant** of a call that completes. An aborted call can leave a
landed pair half read, so the second half of the invariant needs the result. -/
theorem scan_pairInv (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none) :
    ∀ attempts budget (s : DebtState HashInput HashOutput Coordinate) (ρ : Randomness),
      PairInv parameter data message s →
      ∀ out ∈ support (interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget s),
        ∀ r, out.1.1 = some r → PairInv parameter data message out.2 := by
  intro attempts
  induction attempts with
  | zero =>
      intro budget s ρ hinv out hout _ _
      change out ∈ support (interp tg initial model (pure none) budget s) at hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout]
      exact hinv
  | succ attempts ih =>
      intro budget s ρ hinv out hout r hr
      rw [signCostSourceLoop_succ, interp_ordinary] at hout
      split_ifs at hout with h1
      · rw [ordinaryStep, hparse ρ firstCall] at hout
        simp only at hout
        rw [support_bind] at hout
        obtain ⟨res, hres, hout⟩ := Set.mem_iUnion₂.1 hout
        rw [support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        simp only at hr
        show PairInv parameter data message o.2
        have hstep : res.2.cache (blk parameter data message ρ) = some res.1 ∧
            (∀ x, x ≠ blk parameter data message ρ → res.2.cache x = s.cache x) ∧
            (res.2 = s ∨ res.2 = s.store (blk parameter data message ρ) res.1) := by
          cases hc0 : s.cache (blk parameter data message ρ) with
          | some v =>
              rw [readOutside_cached _ s v hc0, support_pure, Set.mem_singleton_iff] at hres
              rw [hres]
              exact ⟨hc0, fun _ _ => rfl, Or.inl rfl⟩
          | none =>
              rw [readOutside_fresh _ s hc0, support_map] at hres
              obtain ⟨v, _, rfl⟩ := hres
              exact ⟨by simp [DebtState.store], fun x hx => store_cache_ne s _ x hx v, Or.inr rfl⟩
        obtain ⟨hb0, hrest, hres2⟩ := hstep
        by_cases hl : Landed parameter (blockIndex res.1)
        · rw [if_pos hl] at ho
          have hkeep := finish_keeps_msg tg initial model parameter data message ρ (budget - 1) res.2 o ho
          have hall := finish_pcache tg initial model parameter data message hparse ρ (budget - 1) res.2 o ho
            (by rw [hr]; simp)
          intro ρ'
          by_cases hρ : ρ' = ρ
          · refine ⟨fun h call => ?_, fun _ _ _ call => by rw [hρ]; exact hall call⟩
            exfalso
            have hs := hall firstCall
            rw [hρ] at h
            rw [show o.2.cache (pblk parameter data message ρ firstCall) = none from h] at hs
            simp at hs
          · have hcall : ∀ call, o.2.cache (pblk parameter data message ρ' call) =
                s.cache (pblk parameter data message ρ' call) := fun call =>
              (hkeep _ (msgInput_digestInput parameter data.root message ρ' call)
                fun c' => pblk_ne_of_ne parameter data message hρ call c').trans
                (hrest _ (pblk_ne_of_ne parameter data message hρ call firstCall))
            refine ⟨fun h call => (hcall call).trans ((hinv ρ').1 ((hcall firstCall).symm.trans h) call),
              fun v h0 hland call => ?_⟩
            rw [hcall call]
            exact (hinv ρ').2 v ((hcall firstCall).symm.trans h0) hland call
        · rw [if_neg hl] at ho
          have hinv1 : PairInv parameter data message res.2 := by
            rcases hres2 with h | h
            · rw [h]; exact hinv
            · rw [h]; exact pairInv_store parameter data message s hinv ρ res.1 hl
          exact ih _ res.2 _ hinv1 o ho r hr
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hr
        cases hr

/-- **The scan signer keeps fresh pairs whole.** -/
theorem source_pairFresh (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (budget : ℕ) (s : DebtState HashInput HashOutput Coordinate)
    (hfresh : PairFresh parameter data message s) :
    ∀ out ∈ support (interp tg initial model (signCostSource parameter data message) budget s),
      PairFresh parameter data message out.2 := by
  intro out hout
  unfold signCostSource at hout
  rw [interp_liftProb_bind, support_bind] at hout
  obtain ⟨ρ, _, hout⟩ := Set.mem_iUnion₂.1 hout
  exact scan_pairFresh tg initial model parameter data message hparse _ budget s ρ hfresh out hout

/-- **The scan signer keeps the pair invariant** of a call that completes. -/
theorem source_pairInv (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (budget : ℕ) (s : DebtState HashInput HashOutput Coordinate)
    (hinv : PairInv parameter data message s) :
    ∀ out ∈ support (interp tg initial model (signCostSource parameter data message) budget s),
      ∀ r, out.1.1 = some r → PairInv parameter data message out.2 := by
  intro out hout r hr
  unfold signCostSource at hout
  rw [interp_liftProb_bind, support_bind] at hout
  obtain ⟨ρ, _, hout⟩ := Set.mem_iUnion₂.1 hout
  exact scan_pairInv tg initial model parameter data message hparse _ budget s ρ hinv out hout r hr

/-- The scan only queries message inputs of the signed message. -/
theorem avoids_scan :
    ∀ attempts ρ, Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate)
      (fun x => IsMsgInput x ∧ ∀ ρ call, x ≠ pblk parameter data message ρ call)
      (signCostSourceLoop parameter data message (data.step message) attempts ρ) := by
  intro attempts
  induction attempts with
  | zero => intro ρ; exact avoids_pure _ _
  | succ attempts ih =>
      intro ρ
      rw [signCostSourceLoop_succ]
      refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun first => ?_⟩
      · cases hb
        exact hx.2 ρ firstCall rfl
      · split_ifs
        · rw [finishCostSource_eq]
          exact avoids_bind _ (avoids_sequenceFin _ _ fun call =>
            avoids_read _ _ fun hx => hx.2 ρ call rfl)
            fun _ => avoids_mono (fun x hx => hx.1) (avoids_finishRest parameter data message ρ _)
        · exact ih _

theorem avoids_source :
    Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate)
      (fun x => IsMsgInput x ∧ ∀ ρ call, x ≠ pblk parameter data message ρ call)
      (signCostSource parameter data message) :=
  avoids_bind _ (avoids_liftProb _ _) fun ρ => avoids_scan parameter data message _ ρ

end Post

end FORS.Security.GraphView
