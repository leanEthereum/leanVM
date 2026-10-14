import Whir.CausalBadEvents

/-! Prefix extensionality for every actual indivisible WHIR challenge, including
its final scalar that has no subsequent prover response. -/
namespace Whir.CausalPrefix
open Concrete Protocol CausalGame CausalProbability CausalPositions
open Classical

private def pre (c : Config) : List (Coordinate c) :=
  [.initial] ++ (List.range c.folds.size).flatMap (levelCoordinates c)

private theorem level_mem_pre {c : Config} (i : Fin c.folds.size) (q : Coordinate c)
    (h : q ∈ levelCoordinates c i.val) : q ∈ pre c := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨i.val, List.mem_range.mpr i.isLt, h⟩

private theorem tail_not_pre {c : Config} (j : Fin (c.logN - c.folds.toList.sum)) :
    Coordinate.tail j ∉ pre c := by
  simp only [pre, List.mem_append, List.mem_singleton, List.mem_flatMap]
  rintro (impossible | ⟨i, _, member⟩)
  · cases impossible
  · unfold levelCoordinates at member
    split_ifs at member <;> simp at member

private theorem pre_length (c : Config) (t : Tape c) :
    (pre c).length = tailStart c (challenges c t) := by
  have size : (challenges c t).tail.size = c.logN - c.folds.toList.sum := by simp [challenges]
  have lengths := congrArg List.length (visibleCoordinates_map c t)
  simp only [List.length_map, visibleCoordinates, visibleBatches, List.length_append,
    List.length_cons, List.length_nil, List.length_ofFn, size] at lengths
  simp only [pre, List.length_append, List.length_cons, List.length_nil, tailStart, levelStart]
  omega

private def tailIndex {c : Config} : Coordinate c → Nat
  | .tail j => j.val
  | _ => 0

/-- The invisible last tail challenge occupies the unique next position after the visible stream. -/
theorem position_tail {c : Config} (j : Fin (c.logN - c.folds.toList.sum)) (t : Tape c) :
    position (.tail j) = tailStart c (challenges c t) + j.val := by
  unfold position visibleCoordinates
  change (pre c ++ List.ofFn (fun k : Fin (c.logN - c.folds.toList.sum - 1) =>
    Coordinate.tail ⟨k.val, by omega⟩)).idxOf (Coordinate.tail j) = _
  rw [List.idxOf_append_of_notMem (tail_not_pre j), pre_length c t]
  congr 1
  let f : Fin (c.logN - c.folds.toList.sum - 1) → Coordinate c :=
    fun k => .tail ⟨k.val, by omega⟩
  change (List.ofFn f).idxOf (.tail j) = j.val
  by_cases h : j.val < c.logN - c.folds.toList.sum - 1
  · have member : Coordinate.tail j ∈ List.ofFn f := List.mem_ofFn.mpr ⟨⟨j.val, h⟩, rfl⟩
    have atIndex := List.getElem_idxOf (List.idxOf_lt_length_of_mem member)
    simp only [List.getElem_ofFn] at atIndex
    simpa only [f, tailIndex] using congrArg tailIndex atIndex
  · rw [List.idxOf_of_notMem ?_, List.length_ofFn]
    · omega
    · simp only [List.mem_ofFn, not_exists]
      intro k equal
      have same := congrArg tailIndex equal
      simp only [f, tailIndex] at same
      have bound := k.isLt
      omega

private theorem fold_mem_level {c : Config} (i : Fin c.folds.size) (j : Fin c.folds[i.val]!) :
    Coordinate.fold i j ∈ levelCoordinates c i.val := by
  unfold levelCoordinates
  rw [dite_eq_left i.isLt]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j, rfl⟩))

theorem visible_or_last {c : Config} (q : Coordinate c) :
    q ∈ visibleCoordinates c ∨ ∃ j : Fin (c.logN - c.folds.toList.sum),
      q = .tail j ∧ j.val + 1 = c.logN - c.folds.toList.sum := by
  cases q with
  | initial => exact Or.inl (by simp [visibleCoordinates])
  | fold i j =>
    left
    apply List.mem_append_left
    exact level_mem_pre i _ (fold_mem_level i j)
  | ood i j =>
    left
    apply List.mem_append_left
    exact level_mem_pre i _ (by simp [levelCoordinates, i.isLt])
  | query i =>
    left
    apply List.mem_append_left
    exact level_mem_pre i _ (by simp [levelCoordinates, i.isLt])
  | tail j =>
    by_cases h : j.val < c.logN - c.folds.toList.sum - 1
    · left
      exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨⟨j.val, h⟩, rfl⟩)
    · exact Or.inr ⟨j, rfl, by omega⟩

/-- Distinct dependent challenge alphabets never occupy the same protocol position. -/
theorem position_injective (c : Config) : Function.Injective (@position c) := by
  intro q r same
  by_cases hq : q ∈ visibleCoordinates c
  · exact (List.idxOf_inj hq).mp same
  by_cases hr : r ∈ visibleCoordinates c
  · exact ((List.idxOf_inj hr).mp same.symm).symm
  obtain ⟨j, rfl, hj⟩ := (visible_or_last q).resolve_left hq
  obtain ⟨k, rfl, hk⟩ := (visible_or_last r).resolve_left hr
  congr 1
  apply Fin.ext
  omega

private theorem pre_position {c : Config} (q : Coordinate c) (t : Tape c) (h : q ∈ pre c) :
    position q < tailStart c (challenges c t) := by
  unfold position visibleCoordinates
  change (pre c ++ List.ofFn (fun k : Fin (c.logN - c.folds.toList.sum - 1) =>
    Coordinate.tail ⟨k.val, by omega⟩)).idxOf q < _
  rw [List.idxOf_append_of_mem h, ← pre_length c t]
  exact List.idxOf_lt_length_of_mem h

private theorem before_tail_or_tail {c : Config} (q : Coordinate c) (t : Tape c) :
    position q < tailStart c (challenges c t) ∨
      ∃ j : Fin (c.logN - c.folds.toList.sum), q = .tail j := by
  cases q with
  | initial => exact Or.inl (pre_position _ t (by simp [pre]))
  | fold i j => exact Or.inl (pre_position _ t (level_mem_pre i _ (fold_mem_level i j)))
  | ood i j => exact Or.inl (pre_position _ t (level_mem_pre i _ (by simp [levelCoordinates, i.isLt])))
  | query i => exact Or.inl (pre_position _ t (level_mem_pre i _ (by simp [levelCoordinates, i.isLt])))
  | tail j => exact Or.inr ⟨j, rfl⟩

private theorem tail_kernels_set_future (input : Public) (strategy : Strategy)
    (valid : input.config.valid = true) (t : Tape input.config)
    (j k : Fin (input.config.logN - input.config.folds.toList.sum)) (x : E)
    (later : j.val < k.val) :
    CausalTerminal.candidate input strategy (set (.tail k) t x) j =
        CausalTerminal.candidate input strategy t j ∧
      CausalTerminal.pending input strategy (set (.tail k) t x) j =
        CausalTerminal.pending input strategy t j := by
  apply CausalTerminal.kernels_congr input strategy valid _ t j
  · simp only [set_tail]
  · exact (tail_challenges_prefix k t x).1
  · intro m hm
    have hmn : m < input.config.logN - input.config.folds.toList.sum := by omega
    have hne : (⟨m, hmn⟩ : Fin (input.config.logN - input.config.folds.toList.sum)) ≠ k :=
      Fin.ne_of_val_ne (by change m ≠ k.val; omega)
    simp only [set_tail, challenges]
    rw [getElem!_pos _ _ (by simpa only [Array.size_ofFn] using hmn),
      getElem!_pos _ _ (by simpa only [Array.size_ofFn] using hmn)]
    simp only [Array.getElem_ofFn, Function.update_of_ne hne]
  · have starts : tailStart input.config (challenges input.config (set (.tail k) t x)) =
        tailStart input.config (challenges input.config t) :=
      levelStart_set (.tail k) t x input.config.folds.size
    rw [starts]
    have shortened := congrArg (List.take (tailStart input.config (challenges input.config t) + j.val))
      (tail_visible_prefix k t x)
    simpa only [List.take_take, Nat.min_eq_left (by omega :
      tailStart input.config (challenges input.config t) + j.val ≤
        tailStart input.config (challenges input.config t) + k.val)] using shortened

/-- A later random coordinate cannot change an already determined bad-prefix event. -/
theorem event_set_future (input : Public) (strategy : Strategy)
    (valid : input.config.valid = true) (q r : Coordinate input.config)
    (t : Tape input.config) (x : Sample r) (later : position q < position r) :
    CausalBadEvents.Bad input strategy q (set r t x) ↔ CausalBadEvents.Bad input strategy q t := by
  cases q with
  | initial =>
    exact CausalInitial.event_set input t r x (by
      intro equal
      subst r
      omega)
  | fold i j =>
    apply CausalFolds.event_set input strategy i j r t x
    rw [position_fold i j t] at later
    omega
  | ood i j =>
    change CausalBoundary.OodEvent input strategy i j (set r t x) ↔
      CausalBoundary.OodEvent input strategy i j t
    rw [CausalBoundary.oodEvent_set_future input strategy t i j r x later]
  | query i =>
    change CausalBoundary.QueryEvent input strategy i (set r t x) ↔
      CausalBoundary.QueryEvent input strategy i t
    apply Iff.of_eq
    apply CausalBoundary.queryEvent_set_future input strategy t i r x
    have shapes := TapeValidity.level_shapes input.config t i i.isLt
    rw [CausalRefinement.levelStart_succ, shapes.1, shapes.2.1]
    rw [position_query i t] at later
    omega
  | tail j =>
    obtain earlier | ⟨k, rfl⟩ := before_tail_or_tail r t
    · rw [position_tail j t] at later
      omega
    · have jk : j.val < k.val := by
        simpa only [position_tail j t, position_tail k t, Nat.add_lt_add_iff_left] using later
      have kernels := tail_kernels_set_future input strategy valid t j k x jk
      have draw : (set (.tail k) t x).2.2 j = t.2.2 j :=
        get_set_ne (.tail k) (.tail j) t x (by
          intro equal
          have same := congrArg tailIndex equal
          simp only [tailIndex] at same
          omega)
      simp only [CausalBadEvents.Bad, kernels.1, kernels.2, draw]

theorem finite_pred_congr {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    (P : ((i : I) → A i) → Prop) (locked : I → Prop)
    (step : ∀ f i, ¬ locked i → ∀ x, P (Function.update f i x) ↔ P f)
    (f g : (i : I) → A i) (same : ∀ i, locked i → f i = g i) : P f ↔ P g := by
  have repair (s : Finset I) : ∀ f g : (i : I) → A i,
      (∀ i, i ∉ s → f i = g i) →
      (∀ i, locked i → f i = g i) → (P f ↔ P g) := by
    induction s using Finset.induction_on with
    | empty =>
      intro f g outside _
      have equal : f = g := funext fun i => outside i (by simp)
      rw [equal]
    | @insert i s absent ih =>
      intro f g outside fixed
      by_cases equal : f i = g i
      · apply ih f g ?_ fixed
        intro j hj
        by_cases ji : j = i
        · subst j; exact equal
        · exact outside j (by simp [hj, ji])
      · have unlocked : ¬ locked i := fun h => equal (fixed i h)
        let mid := Function.update f i (g i)
        have outside' : ∀ j, j ∉ s → mid j = g j := by
          intro j hj
          by_cases ji : j = i
          · subst j; simp [mid]
          · simpa only [mid, Function.update_of_ne ji] using outside j (by simp [hj, ji])
        have fixed' : ∀ j, locked j → mid j = g j := by
          intro j hj
          have ji : j ≠ i := by intro equal; subst j; exact unlocked hj
          simpa only [mid, Function.update_of_ne ji] using fixed j hj
        exact (step f i unlocked (g i)).symm.trans (ih mid g outside' fixed')
  exact repair Finset.univ f g (by intro i impossible; simp at impossible) same

/-- The actual bad event depends only on challenge coordinates through its current position.
No future tape or hidden oracle table is supplied to a prefix adversary. -/
theorem bad_congr (input : Public) (strategy : Strategy) (valid : input.config.valid = true)
    (q : Coordinate input.config) (t u : Tape input.config)
    (same : ∀ r, position r ≤ position q → get r t = get r u) :
    CausalBadEvents.Bad input strategy q t ↔ CausalBadEvents.Bad input strategy q u := by
  let P := fun f : (r : Coordinate input.config) → Sample r =>
    CausalBadEvents.Bad input strategy q ((coordinates input.config).symm f)
  have step : ∀ f r, ¬ position r ≤ position q → ∀ x,
      P (Function.update f r x) ↔ P f := by
    intro f r future x
    have replaced : (coordinates input.config).symm (Function.update f r x) =
        set r ((coordinates input.config).symm f) x := by
      simp only [CausalProbability.set, Equiv.apply_symm_apply]
    dsimp only [P]
    rw [replaced]
    exact event_set_future input strategy valid q r _ x (Nat.lt_of_not_ge future)
  have result := finite_pred_congr P (fun r => position r ≤ position q) step
    (coordinates input.config t) (coordinates input.config u) same
  simpa only [P, Equiv.symm_apply_apply] using result

end Whir.CausalPrefix
