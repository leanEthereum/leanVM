import Whir.CausalGame
import Whir.SamplingRefinement

/-! Every typed field tape is accepted by the concrete challenge-shape validator.
The prefix-sum invariant connects both mutable dimension loops to `remaining`;
there is no rejection or conditioning on sampled field values. -/
namespace Whir.TapeValidity
open Concrete Protocol CausalGame

private def before (c : Config) (i : Nat) : Nat :=
  c.logN - (c.folds.toList.take i).sum

private theorem before_step (c : Config) (i : Nat) (hi : i < c.folds.size) :
    before c i - c.folds[i]! = before c (i + 1) := by
  simp [before, List.take_add_one, getElem?_pos, getElem!_pos, hi, Nat.sub_sub]

private def configStep (c : Config) (i : Nat) (s : Option Bool × Nat) :
    Id (ForInStep (Option Bool × Nat)) := do
  let n := s.2
  if c.folds[i]! == 0 || c.folds[i]! >= n || c.rates[i]! == 0 || c.queries[i]! == 0 then
    return .done (some false, n)
  let n := n - c.folds[i]!
  if n + c.rates[i]! >= 64 then return .done (some false, n)
  return .yield (none, n)

private theorem config_loop_bounds (c : Config) (len start : Nat)
    (hr : start + len ≤ c.folds.size)
    (h : ((forIn (List.range' start len) (none, before c start) (configStep c)).run.1).getD true = true) :
    ∀ i, start ≤ i → i < start + len →
      1 ≤ remaining c i + c.rates[i]! ∧ remaining c i + c.rates[i]! ≤ 64 := by
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
        have hstep := before_step c start hi
        simp only [pure_bind] at h
        rw [hstep] at h
        intro i hlo hhi
        by_cases he : i = start
        · subst i
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hg
          change 1 ≤ before c (start + 1) + c.rates[start]! ∧
            before c (start + 1) + c.rates[start]! ≤ 64
          rw [← hstep]
          omega
        · exact ih (start + 1) (by omega) h i (by omega) (by omega)

/-- Actual `Config.valid` certifies all query depths used by the typed tape. -/
theorem config_query_depth (c : Config) (hc : c.valid = true)
    (i : Nat) (hi : i < c.folds.size) :
    1 ≤ remaining c i + c.rates[i]! ∧ remaining c i + c.rates[i]! ≤ 64 := by
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
    exact config_loop_bounds c c.folds.size 0 (by omega) hloop i (by omega) (by omega)

/-- Typed levels carry exactly the folds, OOD points and squeeze words requested. -/
theorem level_shapes (c : Config) (tape : Tape c) (i : Nat) (hi : i < c.folds.size) :
    let l := (challenges c tape).levels[i]!
    l.folds.size = c.folds[i]! ∧ l.oodPoints.size = oodCount c i ∧
      (∀ p ∈ l.oodPoints, p.size = remaining c i) ∧
      l.querySqueezes.size = queryChunks c i := by
  simp [challenges, getElem!_pos, hi]

/-- Every typed level's sampler succeeds, without examining or restricting its E values. -/
theorem queries_succeed (c : Config) (hc : c.valid = true) (tape : Tape c)
    (i : Nat) (hi : i < c.folds.size) :
    (deriveQueries (remaining c i + c.rates[i]!) c.queries[i]!
      (challenges c tape).levels[i]!.querySqueezes).isNone = false := by
  have hd := config_query_depth c hc i hi
  have hs := (level_shapes c tape i hi).2.2.2
  rw [SamplingRefinement.deriveQueries_eq _ _ _ hd.1 hd.2 (by
    simpa [queryChunks] using hs)]
  rfl

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

private theorem challenge_step (c : Config) (hc : c.valid = true) (tape : Tape c)
    (i : Nat) (hi : i < c.folds.size) :
    challengeStep c (challenges c tape) i (none, before c i) =
      pure (.yield (none, before c (i + 1))) := by
  have hs := level_shapes c tape i hi
  have hq := queries_succeed c hc tape i hi
  unfold challengeStep
  dsimp only
  rw [before_step c i hi]
  change (if _ then _ else if _ then _ else if _ then _ else _) = _
  have ha : ((challenges c tape).levels[i]!.oodPoints.all
      fun p => p.size == before c (i + 1)) = true := by
    apply Array.all_eq_true.mpr
    intro j hj
    exact beq_iff_eq.mpr (hs.2.2.1 _ (Array.getElem_mem hj))
  have hb : ((challenges c tape).levels[i]!.folds.size != c.folds[i]! ||
      (challenges c tape).levels[i]!.oodPoints.size !=
        if i + 1 < c.folds.size then c.oodCounts[i + 1]! else 0) = false := by
    simp [hs.1, hs.2.1, oodCount]
  simp only [hb, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [show before c (i + 1) = remaining c i from rfl, hq,
    Bool.false_eq_true, ↓reduceIte]

private theorem challenge_loop (c : Config) (hc : c.valid = true) (tape : Tape c)
    (len start : Nat) (hr : start + len ≤ c.folds.size) :
    forIn (List.range' start len) (none, before c start)
      (challengeStep c (challenges c tape)) =
        pure (none, before c (start + len)) := by
  induction len generalizing start with
  | zero => simp
  | succ len ih =>
    rw [List.range'_succ, List.forIn_cons, challenge_step c hc tape start (by omega)]
    simp only [pure_bind]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (start + 1) (by omega)

/-- All raw typed tapes satisfy the actual imperative challenge validator.
This is universal over field values, not a success-conditioned distribution. -/
theorem challenges_valid (c : Config) (hc : c.valid = true) (tape : Tape c) :
    (challenges c tape).valid c = true := by
  have hz : before c 0 = c.logN := by simp [before]
  have hl := challenge_loop c hc tape c.folds.size 0 (by omega)
  rw [hz] at hl
  unfold challengeStep at hl
  have hsize : (challenges c tape).levels.size = c.folds.size := by simp [challenges]
  unfold Challenges.valid
  simp only [hc, Bool.not_true, hsize, bne_self_eq_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  dsimp only [Id.run, Bind.bind, Pure.pure] at hl ⊢
  rw [hl]
  have ht : c.folds.toList.take c.folds.size = c.folds.toList := by
    simp [← Array.length_toList]
  simp [before, challenges, ht]

end Whir.TapeValidity
