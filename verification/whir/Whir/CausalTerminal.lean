import Whir.CausalRefinement
import Whir.TerminalSoundness
import Whir.CausalProbability

namespace Whir.CausalTerminal
open Concrete Protocol CausalGame CausalRefinement OperationalRefinement TerminalSoundness

/-- Total wire projections; acceptance separately enforces the parser tags. -/
def proof (input : Public) (strategy : Strategy) (t : Tape input.config) : Opening :=
  decodedOpening input.config (challenges input.config t)
    (run strategy input [] (visibleBatches input.config t.1 (challenges input.config t))).toArray

/-- Actual checked execution up to, but not including, the terminal folds. -/
def beforeChecked (input : Public) (strategy : Strategy) (t : Tape input.config) :
    Except String CheckedState := do
  let ch := challenges input.config t
  let p := proof input strategy t
  let claim := batchClaims (2^input.config.logN) input.claims t.1
  let initial ← initializeVerifier input.config ch input.lanes (liftRoot input.root)
    claim.weight claim.value p
  replayLevels input.config ch p initial

/-- Totalization never accepts an error: the event below requires the actual experiment. -/
def before (input : Public) (strategy : Strategy) (t : Tape input.config) : VerifierState E :=
  ((beforeChecked input strategy t).toOption.getD default).state

def candidate (input : Public) (strategy : Strategy) (t : Tape input.config) (j : Nat) : Array E :=
  residualAt (challenges input.config t) (proof input strategy t).residual j

def pending (input : Public) (strategy : Strategy) (t : Tape input.config) (j : Nat) : VerifierState E :=
  stateAt (challenges input.config t) (proof input strategy t) (before input strategy t) j

private theorem levelStart_mono (ch : Challenges) {i k : Nat} (h : i ≤ k) :
    levelStart ch i ≤ levelStart ch k := by
  induction h with
  | refl => exact le_rfl
  | @step k h ih => rw [levelStart_succ]; omega

private theorem answer_prefix (strategy : Strategy) (input : Public) (left right : List Batch)
    (n k : Nat) (hn : n < k) (h : left.take k = right.take k) :
    (run strategy input [] left).toArray[n]! = (run strategy input [] right).toArray[n]! := by
  have he : left.take (n+1) = right.take (n+1) := by
    have := congrArg (List.take (n+1)) h
    simpa [List.take_take, Nat.min_eq_left (by omega : n+1 ≤ k)] using this
  simpa using field_prefix id strategy input left right n he

/-- Before the tail starts, every level, residual, and initial projection is fixed.
This is a statement about arbitrary replies, including malformed wire tags. -/
theorem decoded_prefix (c : Config) (left right : Challenges)
    (levels : left.levels = right.levels) (strategy : Strategy) (input : Public)
    (bs ds : List Batch) (h : bs.take (tailStart c left) = ds.take (tailStart c left)) :
    let p := decodedOpening c left (run strategy input [] bs).toArray
    let q := decodedOpening c right (run strategy input [] ds).toArray
    p.initial = q.initial ∧ p.levels = q.levels ∧ p.residual = q.residual := by
  have starts : levelStart left = levelStart right := by
    funext i
    simp [levelStart, levelBatches, levels]
  have ans (n : Nat) (hn : n < tailStart c left) :=
    answer_prefix strategy input bs ds n (tailStart c left) hn h
  have lastBound (i : Nat) (hi : i < c.folds.size) :
      levelStart left i + left.levels[i]!.folds.size + left.levels[i]!.oodPoints.size <
        tailStart c left := by
    have hm := levelStart_mono left (Nat.succ_le_of_lt hi)
    rw [levelStart_succ] at hm
    unfold tailStart
    omega
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp only [decodedOpening]
    rw [ans 0 (by have := levelStart_mono left (Nat.zero_le c.folds.size)
                  rw [levelStart_zero] at this; exact this)]
  · simp only [decodedOpening]
    apply congrArg Array.ofFn
    funext i
    have hb := lastBound i i.isLt
    simp only [decodedLevel, ← levels, ← starts]
    congr 1
    · apply Array.ext
      · simp [levels]
      intro j hj hk
      simp only [Array.size_ofFn] at hj
      simp only [Array.getElem_ofFn]
      rw [ans _ (by omega)]
    · split_ifs <;> try rfl
      rw [ans _ (by omega)]
    · apply Array.ext
      · simp [levels]
      intro j hj hk
      simp only [Array.size_ofFn] at hj
      simp only [Array.getElem_ofFn]
      rw [ans _ (by omega)]
    · rw [ans _ hb]
    · rw [ans _ hb]
  · simp only [decodedOpening, ← levels, ← starts]
    split_ifs with hp
    · have hb := lastBound (c.folds.size-1) (by omega)
      rw [ans _ (by omega)]
    · rfl

/-- Checked initialization and replay read no terminal challenge values. -/
theorem before_congr (input : Public) (strategy : Strategy)
    (valid : input.config.valid = true) (t u : Tape input.config)
    (initial : t.1 = u.1)
    (levels : (challenges input.config t).levels = (challenges input.config u).levels)
    (samePrefix :
      (visibleBatches input.config t.1 (challenges input.config t)).take
        (tailStart input.config (challenges input.config t)) =
      (visibleBatches input.config u.1 (challenges input.config u)).take
        (tailStart input.config (challenges input.config t))) :
    before input strategy t = before input strategy u := by
  obtain ⟨hp, hl, hr⟩ := decoded_prefix input.config _ _ levels strategy input _ _ samePrefix
  change (proof input strategy t).initial = (proof input strategy u).initial at hp
  change (proof input strategy t).levels = (proof input strategy u).levels at hl
  change (proof input strategy t).residual = (proof input strategy u).residual at hr
  have init :
      initializeVerifier input.config (challenges input.config t) input.lanes
        (liftRoot input.root) (batchClaims (2^input.config.logN) input.claims t.1).weight
        (batchClaims (2^input.config.logN) input.claims t.1).value (proof input strategy t) =
      initializeVerifier input.config (challenges input.config u) input.lanes
        (liftRoot input.root) (batchClaims (2^input.config.logN) input.claims u.1).weight
        (batchClaims (2^input.config.logN) input.claims u.1).value (proof input strategy u) := by
    simp only [initializeVerifier, TapeValidity.challenges_valid _ valid,
      initial, hp, hl]
    simp [proof, decodedOpening, challenges]
  have replay : replayLevels input.config (challenges input.config t) (proof input strategy t) =
      replayLevels input.config (challenges input.config u) (proof input strategy u) := by
    unfold replayLevels
    have step : verifyLevel input.config (challenges input.config t) (proof input strategy t) =
        verifyLevel input.config (challenges input.config u) (proof input strategy u) := by
      funext i s
      simp only [verifyLevel, levels, hl, hr]
    rw [step]
  simp only [before, beforeChecked, init, replay]

private theorem take_shorter {α : Type*} (a b : List α) {m n : Nat}
    (hm : m ≤ n) (h : a.take n = b.take n) : a.take m = b.take m := by
  have := congrArg (List.take m) h
  simpa [List.take_take, Nat.min_eq_left hm] using this

@[simp] theorem tail_size (c : Config) (t : Tape c) :
    (challenges c t).tail.size = c.logN - c.folds.toList.sum := by
  simp [challenges]

/-- The actual residual and pending state at round `j` depend only on its strict
challenge prefix. The next transmitted message remains completely arbitrary. -/
theorem kernels_congr (input : Public) (strategy : Strategy)
    (valid : input.config.valid = true) (t u : Tape input.config) (j : Nat)
    (initial : t.1 = u.1)
    (levels : (challenges input.config t).levels = (challenges input.config u).levels)
    (past : ∀ k < j, (challenges input.config t).tail[k]! =
      (challenges input.config u).tail[k]!)
    (samePrefix :
      (visibleBatches input.config t.1 (challenges input.config t)).take
        (tailStart input.config (challenges input.config t)+j) =
      (visibleBatches input.config u.1 (challenges input.config u)).take
        (tailStart input.config (challenges input.config t)+j)) :
    candidate input strategy t j = candidate input strategy u j ∧
      pending input strategy t j = pending input strategy u j := by
  have short := take_shorter _ _ (Nat.le_add_right _ j) samePrefix
  have hb := before_congr input strategy valid t u initial levels short
  have hr := (decoded_prefix input.config _ _ levels strategy input _ _ short).2.2
  change (proof input strategy t).residual = (proof input strategy u).residual at hr
  have starts : tailStart input.config (challenges input.config t) =
      tailStart input.config (challenges input.config u) := by
    simp [tailStart, levelStart, levelBatches, levels]
  have messages (k : Nat) (hk : k < j) :
      (proof input strategy t).tailMessages[k]! = (proof input strategy u).tailMessages[k]! := by
    dsimp only [proof, decodedOpening]
    by_cases hlen : k < input.config.logN - input.config.folds.toList.sum - 1
    · rw [getElem!_pos _ _ (by simpa using hlen), getElem!_pos _ _ (by simpa using hlen)]
      simp only [Array.getElem_ofFn]
      rw [← starts]
      exact congrArg tailField (answer_prefix strategy input _ _ _ _ (by omega) samePrefix)
    · rw [getElem!_neg _ _ (by simpa using hlen), getElem!_neg _ _ (by simpa using hlen)]
  have all (k : Nat) (hk : k ≤ j) :
      candidate input strategy t k = candidate input strategy u k ∧
        pending input strategy t k = pending input strategy u k := by
    induction k with
    | zero => exact ⟨hr, hb⟩
    | succ k ih =>
      obtain ⟨ha, hs⟩ := ih (by omega)
      constructor
      · simp only [candidate] at ha ⊢
        rw [residualAt_succ, residualAt_succ, ha, past k (by omega)]
      · simp only [pending] at hs ⊢
        rw [stateAt_succ, stateAt_succ]
        simp only [tailStep, hs, tail_size, past k (by omega), messages k (by omega)]
  exact all j le_rfl

/-- Acceptance identifies the totalized pre-tail kernel with the successful actual
checked replay. Parser failures and verifier failures cannot enter this lemma. -/
theorem accepted_closing (input : Public) (strategy : Strategy) (t : Tape input.config)
    (accepted : experiment input strategy t = true) :
    checkClosing (challenges input.config t) (proof input strategy t)
      (closeTail (challenges input.config t) (proof input strategy t) (before input strategy t)) =
      .ok () := by
  obtain ⟨_, p, s, finish, parsed, init, trace, close⟩ :=
    (experiment_iff input strategy t).mp accepted
  have hp : p = proof input strategy t :=
    opening_eq_decoded _ _ _ _ parsed
  subst p
  have replay := (runChecked_ok_iff_trace _ _ _ _ _).mpr trace
  have hb : beforeChecked input strategy t = .ok finish := by
    simp only [beforeChecked, init]
    exact replay
  have hs : before input strategy t = finish.state := by rw [before, hb]; rfl
  rw [hs, checkClosing_ok_iff]
  exact close

/-- Only accepted executions with a well-shaped false incoming residual claim
are charged. No condition is imposed on rejected or malformed strategy outputs. -/
def Event (input : Public) (strategy : Strategy) (t : Tape input.config) : Prop :=
  experiment input strategy t = true ∧
  (proof input strategy t).residual.size = 2^(input.config.logN-input.config.folds.toList.sum) ∧
  (before input strategy t).weight.size = (proof input strategy t).residual.size ∧
  dot (proof input strategy t).residual (before input strategy t).weight ≠
    (before input strategy t).claim

attribute [local irreducible] collision
set_option maxRecDepth 2048 in
theorem event_has_collision (input : Public) (strategy : Strategy) (t : Tape input.config)
    (h : Event input strategy t) :
    ∃ j : Fin (input.config.logN-input.config.folds.toList.sum),
      dot (candidate input strategy t j) (pending input strategy t j).weight ≠
        (pending input strategy t j).claim ∧
      t.2.2 j ∈ collision (candidate input strategy t j) (pending input strategy t j) := by
  classical
  obtain ⟨ha, shape, weights, lost⟩ := h
  obtain ⟨j, hj, hl, hc⟩ := accepted_has_collision (challenges input.config t)
    (proof input strategy t) (before input strategy t) (by simpa using shape) weights lost
    (accepted_closing input strategy t ha)
  have hn : j < input.config.logN-input.config.folds.toList.sum := by simpa only [tail_size] using hj
  let i : Fin (input.config.logN-input.config.folds.toList.sum) := ⟨j, hn⟩
  have fresh : (challenges input.config t).tail[j]! = t.2.2 i := by
    rw [getElem!_pos (challenges input.config t).tail j hj]
    exact Array.getElem_ofFn hj
  refine ⟨i, hl, ?_⟩
  change t.2.2 i ∈ collision (residualAt (challenges input.config t) (proof input strategy t).residual j)
    (stateAt (challenges input.config t) (proof input strategy t) (before input strategy t) j)
  rw [← fresh]
  exact hc

open CausalProbability

/-- Replacing the fresh actual tape coordinate cannot alter either collision
polynomial, including the adversarial pending message. -/
theorem kernels_set (input : Public) (strategy : Strategy) (valid : input.config.valid = true)
    (j : Fin (input.config.logN-input.config.folds.toList.sum)) (t : Tape input.config) (x : E) :
    candidate input strategy (set (.tail j) t x) j = candidate input strategy t j ∧
      pending input strategy (set (.tail j) t x) j = pending input strategy t j := by
  classical
  apply kernels_congr input strategy valid _ t j
  · simp only [set_tail]
  · exact (tail_challenges_prefix j t x).1
  · intro k hk
    have hkn := lt_trans hk j.isLt
    have hne : (⟨k, hkn⟩ : Fin (input.config.logN-input.config.folds.toList.sum)) ≠ j :=
      Fin.ne_of_val_ne (by simpa using Nat.ne_of_lt hk)
    simp only [set_tail, challenges]
    rw [getElem!_pos _ _ (by simpa only [Array.size_ofFn] using hkn),
      getElem!_pos _ _ (by simpa only [Array.size_ofFn] using hkn)]
    simp only [Array.getElem_ofFn, Function.update_of_ne hne]
  · have hs : tailStart input.config (challenges input.config (set (.tail j) t x)) =
        tailStart input.config (challenges input.config t) := by
      have hl : levelBatches (challenges input.config (set (.tail j) t x)) =
          levelBatches (challenges input.config t) := by
        rw [set_tail]
        rfl
      simp only [tailStart, levelStart, hl]
    rw [hs]
    exact tail_visible_prefix j t x

noncomputable local instance {c : Config} : DecidableEq (Tape c) := Classical.decEq _
noncomputable local instance : DecidableEq E := Classical.decEq _
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Event proof before candidate pending

set_option maxRecDepth 2048
/-- Actual-strategy terminal soundness. Shape and incoming loss are guarded
inside the charged event, not assumed on every possible challenge tape. -/
theorem actual_strategy_bound (input : Public) (strategy : Strategy)
    (valid : input.config.valid = true) :
    Soundness.uniformProb (Finset.univ.filter (Event input strategy)) ≤
      (input.config.logN-input.config.folds.toList.sum : Nat) *
        (2 / (Fintype.card E : ℚ)) := by
  classical
  let n := input.config.logN-input.config.folds.toList.sum
  let bad : Fin n → Tape input.config → Prop := fun j t =>
    dot (candidate input strategy t j) (pending input strategy t j).weight ≠
      (pending input strategy t j).claim ∧
    t.2.2 j ∈ collision (candidate input strategy t j) (pending input strategy t j)
  have sub : Finset.univ.filter (Event input strategy) ⊆
      Finset.univ.biUnion (fun j : Fin n => Finset.univ.filter (bad j)) := by
    simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    intro t ht
    exact event_has_collision input strategy t ht
  have fiber (j : Fin n) (rest : Rest (.tail j)) :
      Soundness.uniformProb (Finset.univ.filter fun x : Sample (.tail j) =>
        bad j (set (.tail j) rest.val x)) ≤ 2 / (Fintype.card E : ℚ) := by
    have eq (x : E) : bad j (set (.tail j) rest.val x) ↔
        dot (candidate input strategy rest.val j) (pending input strategy rest.val j).weight ≠
          (pending input strategy rest.val j).claim ∧
        x ∈ collision (candidate input strategy rest.val j) (pending input strategy rest.val j) := by
      obtain ⟨ha, hs⟩ := kernels_set input strategy valid j rest.val x
      dsimp only [bad]
      rw [ha, hs]
      simp only [set_tail, Function.update_self]
    simp_rw [eq]
    by_cases lost : dot (candidate input strategy rest.val j) (pending input strategy rest.val j).weight ≠
        (pending input strategy rest.val j).claim
    · have he : (Finset.univ.filter fun x : E =>
          dot (candidate input strategy rest.val j) (pending input strategy rest.val j).weight ≠
            (pending input strategy rest.val j).claim ∧
          x ∈ collision (candidate input strategy rest.val j) (pending input strategy rest.val j)) =
          collision (candidate input strategy rest.val j) (pending input strategy rest.val j) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨And.right, fun h => ⟨lost, h⟩⟩
      rw [he]
      exact collision_probability _ _ lost
    · simp only [lost, false_and, Finset.filter_false, Soundness.uniformProb,
        Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  calc
    _ ≤ Soundness.uniformProb (Finset.univ.biUnion
        (fun j : Fin n => Finset.univ.filter (bad j))) := by
      unfold Soundness.uniformProb
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card sub
    _ ≤ ∑ _j : Fin n, 2 / (Fintype.card E : ℚ) :=
      by simpa only using coordinate_union_bound (fun j : Fin n => .tail j) bad _ fiber
    _ = _ := by simp [n]

/-- The current concrete cubic tower has exactly `2^192` elements. -/
theorem actual_strategy_bound_exact (input : Public) (strategy : Strategy)
    (valid : input.config.valid = true) :
    Soundness.uniformProb (Finset.univ.filter (Event input strategy)) ≤
      (input.config.logN-input.config.folds.toList.sum : Nat) * 2 / (2 : ℚ)^192 := by
  have h := actual_strategy_bound input strategy valid
  rw [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] at h
  simpa only [mul_div_assoc] using h

end Whir.CausalTerminal
