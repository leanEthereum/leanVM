/-
  LeanVM.Protocol.EndToEnd.Sound.AvailProb

  The verifier's fresh answers hit the final proof of work with probability at most `2^-127`,
  once in all.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Avail
public import LeanVM.Protocol.EndToEnd.Sound.Extractor
import LeanVM.Protocol.Compile.Rom.Step

/-!
# A fresh hit of the final proof of work is rare

Where the extractor cannot read an accepted proof's challenges off the adversary's queries, a
fresh permutation answer of the verifier hit the final proof of work (`avail_or_hit`). It passes
`17` bits of proof of work and its challenge names the final phase's first positions; at every
admissible shape those are at least `110` bits (`finalBits_all`), so a uniform answer hits with
probability at most `2^-127` (`sum_finalHit_div_le`).

The final proof of work's input is a function of the log (`grindData`) that persists as the log
grows (`grindData_append`), so a fresh query can hit it only once: the potential `Φ`, the hit
plus `2^-127` while that input is not yet logged, never rises in expectation, and starts at most
at `2^-127`. So the verifier's queries hit at most with probability `2^-127` in all
(`prEvent_logged2_hit_le`), not once per query.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The positions' bits -/

theorem firstPositions_succ (d n : ℕ) (c : E) :
    firstPositions d (n + 1) c = firstPositions d n c ++ [(eToNat c >>> (n * d)) % 2 ^ d] := by
  simp [firstPositions, List.range_succ]

/-- The first `n` positions at `depth` bits fix the challenge's low `n · depth` bits. -/
theorem mod_of_firstPositions {d : ℕ} : ∀ {n : ℕ} {c c' : E},
    firstPositions d n c = firstPositions d n c' → eToNat c % 2 ^ (n * d) = eToNat c' % 2 ^ (n * d)
  | 0, _, _, _ => by simp [Nat.mod_one]
  | n + 1, c, c', h => by
    rw [firstPositions_succ, firstPositions_succ] at h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    have ih := mod_of_firstPositions h1
    simp only [List.cons.injEq, and_true, Nat.shiftRight_eq_div_pow] at h2
    rw [Nat.succ_mul, pow_add, Nat.mod_mul, Nat.mod_mul, ih, h2]

theorem eToNat_lt (c : E) : eToNat c < 2 ^ 128 := by
  have h0 : kToNat (c.limb 0) < 2 ^ 64 := UInt64.toNat_lt (K.lane (c.limb 0))
  have h1 : kToNat (c.limb 1) < 2 ^ 64 := UInt64.toNat_lt (K.lane (c.limb 1))
  unfold eToNat
  generalize kToNat (c.limb 0) = a at h0
  generalize kToNat (c.limb 1) = b at h1
  have : (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
  rw [this]
  nlinarith

theorem eToNat_injective : Function.Injective eToNat := by
  intro c c' h
  have hl : ∀ x : E, ∀ i : Fin 2, kToNat (x.limb i) < 2 ^ 64 := fun x i ↦
    UInt64.toNat_lt (K.lane (x.limb i))
  unfold eToNat at h
  have h0 : kToNat (c.limb 0) = kToNat (c'.limb 0) := by
    have := congrArg (· % 2 ^ 64) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hl _ _)] at this
    exact this
  have h1 : kToNat (c.limb 1) = kToNat (c'.limb 1) := by
    have := congrArg (· / 2 ^ 64) h
    simp only [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt (hl _ _),
      zero_add] at this
    exact this
  have hk : ∀ a b : K, kToNat a = kToNat b → a = b := fun a b hab ↦ by
    have hlane : K.lane a = K.lane b := UInt64.toNat_inj.mp hab
    have ha : a = K.ofLane (K.lane a) := rfl
    have hb : b = K.ofLane (K.lane b) := rfl
    rw [ha, hb, hlane]
  rw [← ofLimbs_limb c, ← ofLimbs_limb c', hk _ _ h0, hk _ _ h1]

/-- **At most `2^(128 − n·d)` challenges name given first positions.** -/
theorem card_firstPositions_le (d n : ℕ) (hnd : n * d ≤ 128) (T : List ℕ) :
    (Finset.univ.filter fun c : E ↦ firstPositions d n c = T).card ≤ 2 ^ (128 - n * d) := by
  classical
  have hmap : ∀ c ∈ Finset.univ.filter (fun c : E ↦ firstPositions d n c = T),
      eToNat c / 2 ^ (n * d) ∈ Finset.range (2 ^ (128 - n * d)) := by
    intro c _
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
      Nat.sub_add_cancel hnd]
    exact eToNat_lt c
  have hinj : Set.InjOn (fun c ↦ eToNat c / 2 ^ (n * d))
      (Finset.univ.filter (fun c : E ↦ firstPositions d n c = T) : Set E) := by
    intro c hc c' hc' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc hc'
    have hm := mod_of_firstPositions (hc.trans hc'.symm)
    apply eToNat_injective
    rw [← Nat.div_add_mod (eToNat c) (2 ^ (n * d)), ← Nat.div_add_mod (eToNat c') (2 ^ (n * d))]
    simp only at h
    rw [h, hm]
  exact (Finset.card_le_card_of_injOn _ hmap hinj).trans (Finset.card_range _).le

theorem sum_ind_eq_card {γ : Type} [Fintype γ] (p : γ → Prop) [DecidablePred p] :
    ∑ u, ind (p u) = ((Finset.univ.filter p).card : ℝ≥0∞) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  by_cases h : p u <;> simp [ind, h]

/-- **A uniform challenge names given first positions with probability at most `2^-(n·d)`.** -/
theorem sum_firstPositions_div_le (d n : ℕ) (hnd : n * d ≤ 128) (T : List ℕ) :
    (∑ c : E, ind (firstPositions d n c = T)) / Fintype.card E ≤ 2⁻¹ ^ (n * d) := by
  classical
  rw [sum_ind_eq_card, LeanVM.Protocol.card_E]
  have hc := card_firstPositions_le d n hnd T
  calc ((Finset.univ.filter fun c : E ↦ firstPositions d n c = T).card : ℝ≥0∞) /
        ((2 ^ 128 : ℕ) : ℝ≥0∞)
      ≤ ((2 ^ (128 - n * d) : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = 2⁻¹ ^ (n * d) := by
        have h128 : (2 : ℝ≥0∞) ^ 128 = 2 ^ (128 - n * d) * 2 ^ (n * d) := by
          rw [← pow_add, Nat.sub_add_cancel hnd]
        rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, h128, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (by simp) (by simp), mul_comm (2 ^ (128 - n * d))⁻¹, mul_assoc,
          ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [ind, hp, hq]

/-- **A uniform answer hits a proof of work** of `bits` bits and `n` positions at `d` bits with
probability at most `2^-min(bits, 64) · 2^-(n·d)`. -/
theorem sum_grindHit_div_le (bits d n : ℕ) (hnd : n * d ≤ 128) (phase : List Opening) :
    (∑ u : KeccakState, ind (GrindHit bits d n phase u)) / Fintype.card KeccakState ≤
      2⁻¹ ^ min bits 64 * 2⁻¹ ^ (n * d) := by
  have h := sum_powOk_mul_challengeOf_div_le bits
    fun c ↦ ind (firstPositions d n c = (phase.map Opening.leafIndex).take n)
  simp only [GrindHit, ind_and]
  exact h.trans (by gcongr; exact sum_firstPositions_div_le d n hnd _)

/-! ## The deployed shapes -/

/-- The final level's position bits of a shape's ladder are at least `110`. -/
def finalBitsOK (μ R : ℕ) : Bool :=
  match Whir.ladder μ R with
  | some config =>
    decide (110 ≤ min (128 / finalDepth μ 0 config) (finalCount config) * finalDepth μ 0 config)
  | none => true

/-- **Every shape passes.** -/
theorem finalBits_all : ∀ μ < 31, ∀ R < 5, finalBitsOK μ R = true := by
  decide +kernel

theorem admissible_of_ladder {μ R : ℕ} {config : List Whir.Level}
    (h : Whir.ladder μ R = some config) : Whir.Admissible μ R := by
  by_contra hn
  simp [Whir.ladder, hn] at h

/-- **The final proof of work's data has `110` to `128` position bits.** -/
theorem grindData_bits {bc : List K} {pd : Digest} {π : Proof} {ℓ' : Log} {t : KeccakState}
    {d n : ℕ} {phase : List Opening} (h : grindData bc pd π ℓ' = some (t, d, n, phase)) :
    110 ≤ n * d ∧ n * d ≤ 128 := by
  unfold grindData at h
  obtain ⟨seed, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨config, hconfig, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · obtain ⟨sp1, -, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl, -⟩ := he
    have hadm := admissible_of_ladder hconfig
    have hok := finalBits_all r.1.2.1.1.stackLog
      (by have := hadm.2.1; unfold Whir.maxLogStack at this; omega) r.1.2.1.2
      (by have := hadm.2.2.2; omega)
    simp only [finalBitsOK, hconfig, decide_eq_true_eq] at hok
    refine ⟨hok, ?_⟩
    exact (Nat.mul_le_mul_right _ (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
  · simp at h

/-- **A uniform answer hits the final proof of work after a log with probability at most
`2^-127`.** -/
theorem sum_finalHit_div_le (bc : List K) (pd : Digest) (π : Proof) (ℓ' : Log)
    (t : KeccakState) :
    (∑ u : KeccakState, ind (FinalHit bc pd π ℓ' t u)) / Fintype.card KeccakState ≤ 2⁻¹ ^ 127 := by
  rcases hD : grindData bc pd π ℓ' with _ | ⟨t', d, n, phase⟩
  · refine (avg_le_of_le fun u ↦ ?_).trans zero_le
    refine (ind_of_not ?_).le
    rintro ⟨d, n, phase, h, -⟩
    rw [hD] at h
    cases h
  · obtain ⟨h110, h128⟩ := grindData_bits hD
    have hle : ∀ u, ind (FinalHit bc pd π ℓ' t u) ≤
        ind (GrindHit Whir.queryGrindingBits d n phase u) := fun u ↦ ind_mono fun ⟨d', n', p', h, hg⟩ ↦ by
      rw [hD] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl⟩ := h
      exact hg
    calc (∑ u, ind (FinalHit bc pd π ℓ' t u)) / Fintype.card KeccakState
        ≤ (∑ u, ind (GrindHit Whir.queryGrindingBits d n phase u)) / Fintype.card KeccakState := by
          gcongr with u
          exact hle u
      _ ≤ 2⁻¹ ^ min Whir.queryGrindingBits 64 * 2⁻¹ ^ (n * d) := sum_grindHit_div_le _ _ _ h128 _
      _ = 2⁻¹ ^ (17 + n * d) := by
          rw [show min Whir.queryGrindingBits 64 = 17 by decide, pow_add]
      _ ≤ 2⁻¹ ^ 127 := pow_le_pow_of_le_one zero_le (ENNReal.inv_le_one.2 one_le_two) (by omega)

/-! ## Once in all -/

/-- **A permutation entry at or past `k` answers a hit** of the final proof of work after the log
before it. -/
def HitPast (bc : List K) (pd : Digest) (π : Proof) (k : ℕ) (ℓ : Log) : Prop :=
  ∃ j, k ≤ j ∧ ∃ (hj : j < ℓ.length) (t u : KeccakState), ℓ[j] = .inr (t, u) ∧
    FinalHit bc pd π (ℓ.take j) t u

/-- The final proof of work's input is not a logged input yet. -/
def Pending (bc : List K) (pd : Digest) (π : Proof) (ℓ : Log) : Prop :=
  ¬ ∃ D, grindData bc pd π ℓ = some D ∧ D.1 ∈ fIns ℓ

theorem hitPast_append {bc : List K} {pd : Digest} {π : Proof} {k : ℕ} {ℓ : Log} {e : Entry}
    (h : HitPast bc pd π k (ℓ ++ [e])) :
    HitPast bc pd π k ℓ ∨ ∃ t u, e = .inr (t, u) ∧ FinalHit bc pd π ℓ t u := by
  obtain ⟨j, hkj, hj, t, u, hej, hhit⟩ := h
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
  · left
    refine ⟨j, hkj, hlt, t, u, ?_, ?_⟩
    · rwa [List.getElem_append_left hlt] at hej
    · rwa [List.take_append_of_le_length hlt.le] at hhit
  · right
    refine ⟨t, u, ?_, ?_⟩
    · rwa [List.getElem_append_right (le_refl _), List.getElem_singleton] at hej
    · rwa [List.take_left] at hhit

theorem fIns_append (ℓ : Log) (e : Entry) : fIns ℓ ⊆ fIns (ℓ ++ [e]) := by
  intro x hx
  simp only [fIns, List.mem_map] at hx ⊢
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨p, mem_rightOf.mpr (List.mem_append_left _ (mem_rightOf.mp hp)), rfl⟩

theorem pending_of_append {bc : List K} {pd : Digest} {π : Proof} {ℓ : Log} {e : Entry}
    (h : Pending bc pd π (ℓ ++ [e])) : Pending bc pd π ℓ := by
  rintro ⟨D, hD, hin⟩
  exact h ⟨D, grindData_append hD [e], fIns_append ℓ e hin⟩

/-- **The verifier's queries hit the final proof of work with probability at most `2^-127`**: in
the logged experiment, the probability that the verifier's log does not extend the adversary's,
or that a permutation entry past the adversary's log answers a hit, is at most `2^-127`. -/
theorem prEvent_logged2_hit_le {α : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) (QV : ℕ) (hV : ∀ a, IsTotalQueryBound (V a) QV)
    (bc : α → List K) (pd : α → Digest) (π : α → Proof) :
    Pr{let w ← logged2 A V}[¬ w.1.2 <+: w.2.2 ∨
      HitPast (bc w.1.1) (pd w.1.1) (π w.1.1) w.1.2.length w.2.2] ≤ 2⁻¹ ^ 127 := by
  unfold logged2
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ ↦ ?_
  rw [prEvent_map]
  set B := bc p.1
  set P := pd p.1
  set Q := π p.1
  let Φ : Log → ℝ≥0∞ := fun ℓ ↦
    ind (HitPast B P Q p.2.length ℓ) + 2⁻¹ ^ 127 * ind (Pending B P Q ℓ)
  have hΦ : LogFreshStepBound Φ 0 := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs ↦ ?_⟩
    · rw [add_zero]
      refine avg_le_of_le fun u ↦ add_le_add (ind_mono fun h ↦ ?_) ?_
      · rcases hitPast_append h with h | ⟨t, u', he, -⟩
        · exact h
        · cases he
      · gcongr
        exact ind_mono pending_of_append
    · rw [add_zero]
      by_cases hg : ∃ D, grindData B P Q ℓ = some D ∧ D.1 = s
      · obtain ⟨D, hD, hDs⟩ := hg
        have hpend : Pending B P Q ℓ := by
          rintro ⟨D', hD', hin⟩
          rw [hD] at hD'
          cases hD'
          rw [hDs] at hin
          exact hs hin
        have hstep : ∀ u, Φ (ℓ ++ [.inr (s, u)]) ≤
            (ind (FinalHit B P Q ℓ s u) + ind (HitPast B P Q p.2.length ℓ)) := fun u ↦ by
          have hnp : ¬ Pending B P Q (ℓ ++ [.inr (s, u)]) := fun h ↦ h ⟨D,
            grindData_append hD _, by
              rw [hDs]
              simp only [fIns, rightOf_append, List.map_append, List.mem_append]
              right
              simp [rightOf]⟩
          simp only [Φ, ind_of_not hnp, mul_zero, add_zero]
          refine (ind_mono fun h ↦ ?_).trans (ind_or_le _ _)
          rcases hitPast_append h with h | ⟨t, u', he, hh⟩
          · exact Or.inr h
          · simp only [Sum.inr.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact Or.inl hh
        calc (∑ u, Φ (ℓ ++ [.inr (s, u)])) / Fintype.card KeccakState
            ≤ (∑ u, (ind (FinalHit B P Q ℓ s u) + ind (HitPast B P Q p.2.length ℓ))) /
                Fintype.card KeccakState := by
              gcongr with u
              exact hstep u
          _ = (∑ u, ind (FinalHit B P Q ℓ s u)) / Fintype.card KeccakState +
                ind (HitPast B P Q p.2.length ℓ) := avg_add_const _ _
          _ ≤ 2⁻¹ ^ 127 + ind (HitPast B P Q p.2.length ℓ) := by
              gcongr
              exact sum_finalHit_div_le B P Q ℓ s
          _ = Φ ℓ := by simp only [Φ, ind_of hpend, mul_one, add_comm]
      · refine avg_le_of_le fun u ↦ add_le_add (ind_mono fun h ↦ ?_) ?_
        · rcases hitPast_append h with h | ⟨t, u', he, hh⟩
          · exact h
          · simp only [Sum.inr.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            obtain ⟨d, n, phase, hD, -⟩ := hh
            exact absurd ⟨_, hD, rfl⟩ hg
        · gcongr
          exact ind_mono pending_of_append
  dsimp only
  refine (prEvent_run_loggedRO_le_of_freshStepBound hΦ (V p.1) QV (hV p.1) p.2
    (fun _ ℓ ↦ ¬ p.2 <+: ℓ ∨ HitPast B P Q p.2.length ℓ) ?_).trans ?_
  · intro z hz hev
    have hpre := (simulateQ_look_of_mem_support _ p.2 z hz).1
    rcases hev with hn | hr
    · exact absurd hpre hn
    · exact (ind_of hr).ge.trans le_self_add
  · have h0 : ¬ HitPast B P Q p.2.length p.2 := fun ⟨j, hkj, hj, _⟩ ↦ by omega
    simp only [Φ, ind_of_not h0, zero_add, mul_zero, add_zero]
    exact mul_le_of_le_one_right' (ind_le_one _)

/-! ## The levels' roots -/

/-- At most this many roots in a run of the verifier: every commitment costs two quarters. -/
def rootCap : ℕ := leanVmCost / 2

/-- **A run's commitments are at most half its cost.** -/
theorem commits_length_le_of_costs {α : Type} {height : ℕ} :
    ∀ {p : VerifierProgram α} {n : ℕ} {Q : α → Prop} {l : List Ev} {q : VerifierProgram α},
      VerifierProgram.Costs height p n Q → p.after l = some q → 2 * (commits l).length ≤ n
  | _, _, _, [], _, _, _ => by simp [commits]
  | .ret _, _, _, _ :: _, _, _, ha => by simp [VerifierProgram.after] at ha
  | .fail, _, _, _ :: _, _, _, ha => by simp [VerifierProgram.after] at ha
  | .read k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    have := commits_length_le_of_costs (hc.2 _) ha
    simp only [commits]
    omega
  | .sample k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    have := commits_length_le_of_costs (hc.2 _) ha
    simp only [commits]
    omega
  | .grind b k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    split at ha
    · have := commits_length_le_of_costs hc.2 ha
      simp only [commits]
      omega
    · simp at ha
  | .commit ht w k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    split at ha
    · have := commits_length_le_of_costs hc.2.2 ha
      have h2 := hc.2.1
      simp only [commits, List.length_cons]
      omega
    · simp at ha
  | .query i ps k, n, _, e :: es, _, hc, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    have := commits_length_le_of_costs (hc.2 _) ha
    simp only [commits]
    omega

/-- **The roots the cut verifier's replay reads** on the log `ℓ₀`'s answers, at most `rootCap`. -/
def replayRoots (bc : List K) (pd : Digest) (π : Proof) (ℓ₀ : Log) : List Digest :=
  (((leanVmSeed bc pd).run (lookH ℓ₀) (lookF ℓ₀)).bind fun seed ↦
    (replayU (lookF ℓ₀) (leanVmProgramCut bc pd) (startState π seed)).map fun r ↦
      (r.2.roots.map (·.1)).take rootCap).getD []

theorem length_replayRoots_le (bc : List K) (pd : Digest) (π : Proof) (ℓ₀ : Log) :
    (replayRoots bc pd π ℓ₀).length ≤ rootCap := by
  unfold replayRoots
  rcases (leanVmSeed bc pd).run (lookH ℓ₀) (lookF ℓ₀) with _ | seed
  · simp
  · rcases h : replayU (lookF ℓ₀) (leanVmProgramCut bc pd) (startState π seed) with _ | r
    · simp [h]
    · simp [h]

/-- A hash entry past the adversary's log answers one of the replay's roots. -/
def RootsAnswered (bc : List K) (pd : Digest) (π : Proof) (ℓ₀ ℓ : Log) : Prop :=
  ∃ r ∈ replayRoots bc pd π ℓ₀, ∃ x, .inl (x, r) ∈ ℓ.drop ℓ₀.length

/-- **The verifier rarely answers a root afresh**: the probability that a fresh hash answer of
the verifier, past the adversary's log, is one of the roots the cut verifier's replay reads on the
adversary's answers is at most `rootCap · 2^-256` per verifier query. -/
theorem prEvent_logged2_roots_le {α : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) (QV : ℕ) (hV : ∀ a, IsTotalQueryBound (V a) QV)
    (bc : α → List K) (pd : α → Digest) (π : α → Proof) :
    Pr{let w ← logged2 A V}[¬ w.1.2 <+: w.2.2 ∨
      RootsAnswered (bc w.1.1) (pd w.1.1) (π w.1.1) w.1.2 w.2.2] ≤
      QV * (rootCap * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  unfold logged2
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ ↦ ?_
  rw [prEvent_map]
  set R := replayRoots (bc p.1) (pd p.1) (π p.1) p.2 with hRdef
  have hR : R.length ≤ rootCap := length_replayRoots_le _ _ _ _
  let Φ : Log → ℝ≥0∞ := fun ℓ ↦ ind (∃ r ∈ R, ∃ x, .inl (x, r) ∈ ℓ.drop p.2.length)
  have hdrop : ∀ (ℓ : Log) (e : Entry), (ℓ ++ [e]).drop p.2.length ⊆ ℓ.drop p.2.length ++ [e] := by
    intro ℓ e x hx
    rw [List.drop_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_of_mem_drop hx)
  have hsum : ∑ u : Digest, ind (u ∈ R) ≤ rootCap := by
    calc ∑ u : Digest, ind (u ∈ R) ≤ ∑ u : Digest, (R.map fun r ↦ ind (u = r)).sum := by
          gcongr with u
          exact (ind_mono fun h ↦ ⟨u, h, rfl⟩).trans (ind_exists_le R fun r ↦ u = r)
      _ = (R.map fun r ↦ ∑ u : Digest, ind (u = r)).sum := sum_list_sum_comm R fun r u ↦ ind (u = r)
      _ ≤ R.length * 1 := list_sum_le _ _ _ fun r _ ↦
          sum_ind_le_one fun a b ha hb ↦ ha.trans hb.symm
      _ ≤ rootCap := by rw [mul_one]; exact_mod_cast hR
  have hΦ : LogFreshStepBound Φ (rootCap * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ t _ ↦ ?_, fun ℓ t _ ↦ ?_⟩
    · have hstep : ∀ u, Φ (ℓ ++ [.inl (t, u)]) ≤ ind (u ∈ R) + Φ ℓ := fun u ↦ by
        refine (ind_mono ?_).trans ((ind_or_le _ _).trans (le_of_eq (add_comm _ _)))
        rintro ⟨r, hr, x, hx⟩
        rcases List.mem_append.mp (hdrop ℓ _ hx) with hx | hx
        · exact Or.inl ⟨r, hr, x, hx⟩
        · rw [List.mem_singleton] at hx
          cases hx
          exact Or.inr hr
      calc (∑ u, Φ (ℓ ++ [.inl (t, u)])) / Fintype.card Digest
          ≤ (∑ u, (ind (u ∈ R) + Φ ℓ)) / Fintype.card Digest := by
            gcongr with u
            exact hstep u
        _ = (∑ u, ind (u ∈ R)) / Fintype.card Digest + Φ ℓ := avg_add_const _ _
        _ ≤ rootCap * (2 ^ 256 : ℝ≥0∞)⁻¹ + Φ ℓ := by
            gcongr
            rw [card_digest, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
            gcongr
        _ = Φ ℓ + rootCap * (2 ^ 256 : ℝ≥0∞)⁻¹ := add_comm _ _
    · have hstep : ∀ u, Φ (ℓ ++ [.inr (t, u)]) ≤ Φ ℓ := fun u ↦ by
        refine ind_mono ?_
        rintro ⟨r, hr, x, hx⟩
        rcases List.mem_append.mp (hdrop ℓ _ hx) with hx | hx
        · exact ⟨r, hr, x, hx⟩
        · simp at hx
      exact (avg_le_of_le hstep).trans le_self_add
  dsimp only
  refine (prEvent_run_loggedRO_le_of_freshStepBound hΦ (V p.1) QV (hV p.1) p.2
    (fun _ ℓ ↦ ¬ p.2 <+: ℓ ∨ RootsAnswered (bc p.1) (pd p.1) (π p.1) p.2 ℓ) ?_).trans ?_
  · intro z hz hev
    have hpre := (simulateQ_look_of_mem_support _ p.2 z hz).1
    rcases hev with hn | hr
    · exact absurd hpre hn
    · exact (ind_of hr).ge
  · simp [Φ, ind]

end
end LeanVM.Protocol.EndToEnd.Sound
