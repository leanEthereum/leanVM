import Whir.TapeValidity

/-! Guard facts extracted from the existing imperative validators, for arbitrary
challenge arrays. OOD points belong to the next level, exactly as in the validator. -/
namespace Whir.WHIRNativeGuards
open Concrete Protocol CausalGame

/-- Dimension on entry to level `i`, before its folds. -/
def before (c : Config) (i : Nat) : Nat :=
  c.logN - (c.folds.toList.take i).sum

theorem before_step (c : Config) (i : Nat) (hi : i < c.folds.size) :
    before c i - c.folds[i]! = remaining c i := by
  simp [before, remaining, List.take_add_one, getElem?_pos, getElem!_pos, hi,
    Nat.sub_sub]

/-- Every configuration guard used by one loop iteration. -/
def ConfigLevel (c : Config) (i : Nat) : Prop :=
  0 < c.folds[i]! ∧ c.folds[i]! < before c i ∧
  0 < c.rates[i]! ∧ 0 < c.queries[i]! ∧
  remaining c i + c.rates[i]! < 64

private def configStep (c : Config) (i : Nat) (s : Option Bool × Nat) :
    Id (ForInStep (Option Bool × Nat)) := do
  let n := s.2
  if c.folds[i]! == 0 || c.folds[i]! >= n || c.rates[i]! == 0 || c.queries[i]! == 0 then
    return .done (some false, n)
  let n := n - c.folds[i]!
  if n + c.rates[i]! >= 64 then return .done (some false, n)
  return .yield (none, n)

private theorem config_loop (c : Config) (len start : Nat)
    (hr : start + len ≤ c.folds.size)
    (h : ((forIn (List.range' start len) (none, before c start)
      (configStep c)).run.1).getD true = true) :
    ∀ i, start ≤ i → i < start + len → ConfigLevel c i := by
  induction len generalizing start with
  | zero => intro i hlo hhi; omega
  | succ len ih =>
    have hi : start < c.folds.size := by omega
    simp only [List.range'_succ, List.forIn_cons, configStep] at h
    split at h
    · simp at h
    · rename_i hg
      split at h
      · simp at h
      · rename_i hd
        have hs : before c start - c.folds[start]! = before c (start + 1) :=
          before_step c start hi
        simp only [pure_bind] at h
        rw [hs] at h
        intro i hlo hhi
        by_cases he : i = start
        · subst i
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hg
          dsimp [ConfigLevel]
          rw [← before_step c start hi]
          omega
        · exact ih (start + 1) (by omega) h i (by omega) (by omega)

/-- The actual configuration header checks, without additional acceptance guards. -/
theorem config_header (c : Config) (hc : c.valid = true) :
    2 ≤ c.folds.size ∧ c.rates.size = c.folds.size ∧
    c.queries.size = c.folds.size ∧ c.oodCounts.size = c.folds.size ∧
    c.oodCounts[0]! = 0 := by
  unfold Config.valid at hc
  dsimp only [Id.run] at hc
  split at hc
  · simp at hc
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, not_or, not_not] at h
    omega

/-- Positive folds/rates/query counts, no subtraction underflow, and depth bound. -/
theorem config_level (c : Config) (hc : c.valid = true)
    (i : Nat) (hi : i < c.folds.size) : ConfigLevel c i := by
  unfold Config.valid at hc
  dsimp only [Id.run] at hc
  split at hc
  · simp at hc
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at hc
    have hloop : ((forIn (List.range' 0 c.folds.size) (none, before c 0)
        (configStep c)).run.1).getD true = true := by
      have hz : before c 0 = c.logN := by simp [before]
      rw [hz]
      cases he : (forIn (List.range' 0 c.folds.size) (none, c.logN) (configStep c)).run.1 with
      | none => simp
      | some b =>
        unfold configStep at he
        dsimp only [Id.run, Bind.bind, Pure.pure] at he hc
        rw [he] at hc
        exact hc
    exact config_loop c c.folds.size 0 (by omega) hloop i (by omega) (by omega)

/-- Saved shapes and sampler success checked at an arbitrary challenge level. -/
def ChallengeLevel (c : Config) (ch : Challenges) (i : Nat) : Prop :=
  ch.levels[i]!.folds.size = c.folds[i]! ∧
  ch.levels[i]!.oodPoints.size = oodCount c i ∧
  (∀ p ∈ ch.levels[i]!.oodPoints, p.size = remaining c i) ∧
  (deriveQueries (remaining c i + c.rates[i]!) c.queries[i]!
    ch.levels[i]!.querySqueezes).isNone = false

private def challengeStep (c : Config) (ch : Challenges) (i : Nat)
    (s : Option Bool × Nat) : Id (ForInStep (Option Bool × Nat)) := do
  let n := s.2 - c.folds[i]!
  let l := ch.levels[i]!
  let count := if i + 1 < c.folds.size then c.oodCounts[i + 1]! else 0
  if l.folds.size != c.folds[i]! || l.oodPoints.size != count then
    return .done (some false, n)
  if !(l.oodPoints.all fun p => p.size == n) then return .done (some false, n)
  if (deriveQueries (n + c.rates[i]!) c.queries[i]! l.querySqueezes).isNone then
    return .done (some false, n)
  return .yield (none, n)

private theorem challenge_loop (c : Config) (ch : Challenges) (len start : Nat)
    (hr : start + len ≤ c.folds.size)
    (h : let result := (forIn (List.range' start len) (none, before c start)
      (challengeStep c ch)).run
      result.1.getD (ch.tail.size == result.2) = true) :
    ch.tail.size = before c (start + len) ∧
    ∀ i, start ≤ i → i < start + len → ChallengeLevel c ch i := by
  induction len generalizing start with
  | zero =>
    simp at h
    exact ⟨h, by intro i hlo hhi; omega⟩
  | succ len ih =>
    have hi : start < c.folds.size := by omega
    simp only [List.range'_succ, List.forIn_cons, challengeStep] at h
    rw [← oodCount] at h
    split at h
    · simp at h
    · rename_i hg
      split at h
      · simp at h
      · rename_i hp
        split at h
        · simp at h
        · rename_i hq
          have hs : before c start - c.folds[start]! = before c (start + 1) :=
            before_step c start hi
          simp only [pure_bind] at h
          rw [hs] at h
          have ht := ih (start + 1) (by omega) h
          refine ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht.1, ?_⟩
          intro i hlo hhi
          by_cases he : i = start
          · subst i
            simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hg
            have ha : (ch.levels[start]!.oodPoints.all
                fun p => p.size == before c start - c.folds[start]!) = true := by
              simpa using hp
            have hpoints : ∀ p ∈ ch.levels[start]!.oodPoints,
                p.size = before c start - c.folds[start]! := by
              intro p hmem
              obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hmem
              exact beq_iff_eq.mp ((Array.all_eq_true.mp ha) j hj)
            refine ⟨hg.1, hg.2, ?_, ?_⟩
            · simpa only [before_step c start hi] using hpoints
            · simpa only [before_step c start hi, Bool.not_eq_true] using hq
          · exact ht.2 i (by omega) (by omega)

/-- All shape facts follow from `Challenges.valid` for arbitrary challenge values. -/
theorem challenges_guards (c : Config) (ch : Challenges) (h : ch.valid c = true) :
    c.valid = true ∧ ch.levels.size = c.folds.size ∧
    ch.tail.size = c.logN - c.folds.toList.sum ∧
    ∀ i, i < c.folds.size → ChallengeLevel c ch i := by
  unfold Challenges.valid at h
  dsimp only [Id.run] at h
  split at h
  · simp at h
  · rename_i hh
    simp only [Bool.or_eq_true, Bool.not_eq_true,
      bne_iff_ne, not_or, not_not] at hh
    refine ⟨by simpa using hh.1, hh.2, ?_⟩
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at h
    have hl : let result := (forIn (List.range' 0 c.folds.size) (none, before c 0)
        (challengeStep c ch)).run
        result.1.getD (ch.tail.size == result.2) = true := by
      have hz : before c 0 = c.logN := by simp [before]
      rw [hz]
      unfold challengeStep
      dsimp only [Id.run, Bind.bind, Pure.pure] at h ⊢
      exact h
    have ht := challenge_loop c ch c.folds.size 0 (by omega) hl
    refine ⟨?_, fun i hi => ht.2 i (by omega) (by omega)⟩
    simpa [before, ← Array.length_toList] using ht.1

/-- Each used configuration array index is in bounds. -/
theorem config_indices (c : Config) (hc : c.valid = true)
    (i : Nat) (hi : i < c.folds.size) :
    i < c.rates.size ∧ i < c.queries.size ∧ i < c.oodCounts.size := by
  have hs := config_header c hc
  rw [hs.2.1, hs.2.2.1, hs.2.2.2.1]
  exact ⟨hi, hi, hi⟩

/-- The next-level OOD count is read only at an in-bounds index. -/
theorem config_next_ood_index (c : Config) (hc : c.valid = true)
    (i : Nat) (hi : i + 1 < c.folds.size) :
    i + 1 < c.oodCounts.size :=
  (config_indices c hc (i + 1) hi).2.2

theorem config_remaining (c : Config) (hc : c.valid = true)
    (i : Nat) (hi : i < c.folds.size) :
    0 < remaining c i ∧ remaining c i + c.folds[i]! = before c i := by
  have hk := (config_level c hc i hi).2.1
  rw [← before_step c i hi]
  omega

theorem challenges_config (c : Config) (ch : Challenges) (h : ch.valid c = true) :
    c.valid = true := (challenges_guards c ch h).1

theorem challenges_levels (c : Config) (ch : Challenges) (h : ch.valid c = true) :
    ch.levels.size = c.folds.size := (challenges_guards c ch h).2.1

theorem challenges_tail (c : Config) (ch : Challenges) (h : ch.valid c = true) :
    ch.tail.size = c.logN - c.folds.toList.sum := (challenges_guards c ch h).2.2.1

theorem challenges_level (c : Config) (ch : Challenges) (h : ch.valid c = true)
    (i : Nat) (hi : i < c.folds.size) : ChallengeLevel c ch i :=
  (challenges_guards c ch h).2.2.2 i hi

theorem challenges_folds (c : Config) (ch : Challenges) (h : ch.valid c = true)
    (i : Nat) (hi : i < c.folds.size) :
    ch.levels[i]!.folds.size = c.folds[i]! := (challenges_level c ch h i hi).1

theorem challenges_ood_count (c : Config) (ch : Challenges) (h : ch.valid c = true)
    (i : Nat) (hi : i < c.folds.size) :
    ch.levels[i]!.oodPoints.size = oodCount c i := (challenges_level c ch h i hi).2.1

theorem challenges_ood_point (c : Config) (ch : Challenges) (h : ch.valid c = true)
    (i : Nat) (hi : i < c.folds.size) (p : Array E) (hp : p ∈ ch.levels[i]!.oodPoints) :
    p.size = remaining c i := (challenges_level c ch h i hi).2.2.1 p hp

theorem challenges_queries (c : Config) (ch : Challenges) (h : ch.valid c = true)
    (i : Nat) (hi : i < c.folds.size) :
    (deriveQueries (remaining c i + c.rates[i]!) c.queries[i]!
      ch.levels[i]!.querySqueezes).isNone = false :=
  (challenges_level c ch h i hi).2.2.2

/-- A malformed saved point cannot pass the actual challenge validator. -/
theorem reject_ood_point (c : Config) (ch : Challenges)
    (i : Nat) (hi : i < c.folds.size) (p : Array E) (hp : p ∈ ch.levels[i]!.oodPoints)
    (hsize : p.size ≠ remaining c i) : ch.valid c = false := by
  cases h : ch.valid c with
  | false => rfl
  | true => exact False.elim (hsize (challenges_ood_point c ch h i hi p hp))

end Whir.WHIRNativeGuards
