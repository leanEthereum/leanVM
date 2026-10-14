module

public import LeanVMCircuits.Bus.Basic

@[expose] public section

/-!
# The state walk and the clock

Proposition `prop:walk` and Corollary `cor:clock` of `doc/leanvm/body/06-bus-interactions.tex` (§sec:state).
If the state tuples balance, the rows split into a walk from the initial state to the final one and closed walks
(`exists_walk`, `exists_closedWalks`). With the clock each row pushes, every row's accesses are in order, the walk's
rows are the live ones, the clock of its `i`-th row being `2^40 + 2^5 i`, and every other row's clock lacks the live
bit (`state_walk`).
-/

namespace LeanVMCircuits.Bus

open LeanVMCircuits.Rec

section Walk

variable {ρ α : Type} (pullOf pushOf : ρ → α)

/-- `w` is a walk from `s` to `f`: its first row pulls `s`, each row pushes what the next pulls, the last pushes `f`. -/
def IsWalk : α → α → List ρ → Prop
  | s, f, [] => s = f
  | s, f, r :: w => pullOf r = s ∧ IsWalk (pushOf r) f w

theorem push_add_eq_of_cons {r : ρ} {rows : List ρ} {s f : α} (pull_eq : pullOf r = s)
    (balance : ((r :: rows).map pushOf : Multiset α) + {s} = ((r :: rows).map pullOf : Multiset α) + {f}) :
    (rows.map pushOf : Multiset α) + {pushOf r} = (rows.map pullOf : Multiset α) + {f} := by
  simp only [List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add, pull_eq] at balance
  apply add_right_cancel (b := ({s} : Multiset α))
  calc (rows.map pushOf : Multiset α) + {pushOf r} + {s}
      = {pushOf r} + (rows.map pushOf : Multiset α) + {s} := by abel
    _ = {s} + (rows.map pullOf : Multiset α) + {f} := balance
    _ = (rows.map pullOf : Multiset α) + {f} + {s} := by abel

/--
Proposition `prop:walk`. If the rows' pushed states and the initial state `s` form the same multiset as the rows'
pulled states and the final state `f`, the rows split into a walk from `s` to `f` and rows whose pushed and pulled
states balance among themselves.
-/
theorem exists_walk (rows : List ρ) (s f : α)
    (balance : (rows.map pushOf : Multiset α) + {s} = (rows.map pullOf : Multiset α) + {f}) :
    ∃ walk rest : List ρ, rows.Perm (walk ++ rest) ∧ IsWalk pullOf pushOf s f walk ∧
      (rest.map pushOf : Multiset α) = rest.map pullOf := by
  classical
  induction h : rows.length using Nat.strong_induction_on generalizing rows s with
  | _ n ih =>
  by_cases s_eq : s = f
  · subst s_eq
    exact ⟨ [], rows, List.Perm.refl _, rfl, (add_left_inj _).mp balance ⟩
  have s_mem : s ∈ (rows.map pullOf : Multiset α) + {f} := balance ▸ Multiset.mem_add.mpr (Or.inr (by simp))
  have s_mem_pulls : s ∈ rows.map pullOf := by
    rcases Multiset.mem_add.mp s_mem with s_mem | s_mem
    · exact Multiset.mem_coe.mp s_mem
    · exact absurd (Multiset.mem_singleton.mp s_mem) s_eq
  obtain ⟨ r, r_mem, pull_eq ⟩ := List.mem_map.mp s_mem_pulls
  have perm := List.perm_cons_erase r_mem
  have perm_balance : ((r :: rows.erase r).map pushOf : Multiset α) + {s} =
      ((r :: rows.erase r).map pullOf : Multiset α) + {f} := by
    rwa [← Multiset.coe_eq_coe.mpr (perm.map pushOf), ← Multiset.coe_eq_coe.mpr (perm.map pullOf)]
  have balance' := push_add_eq_of_cons pullOf pushOf pull_eq perm_balance
  have length_lt : (rows.erase r).length < n := by
    rw [List.length_erase_of_mem r_mem, ← h]
    exact Nat.sub_lt (List.length_pos_of_mem r_mem) Nat.one_pos
  obtain ⟨ walk, rest, walk_perm, is_walk, rest_balance ⟩ := ih _ length_lt (rows.erase r) (pushOf r) balance' rfl
  refine ⟨ r :: walk, rest, perm.trans (List.Perm.cons r walk_perm), ⟨ pull_eq, is_walk ⟩, rest_balance ⟩

/-- Rows whose pushed and pulled states balance split into closed walks: the closed walks of `prop:walk`. -/
theorem exists_closedWalks (rows : List ρ) (balance : (rows.map pushOf : Multiset α) = rows.map pullOf) :
    ∃ cycles : List (List ρ), rows.Perm cycles.flatten ∧
      ∀ c ∈ cycles, ∃ r w, c = r :: w ∧ IsWalk pullOf pushOf (pullOf r) (pullOf r) c := by
  induction h : rows.length using Nat.strong_induction_on generalizing rows with
  | _ n ih =>
  cases rows with
  | nil => exact ⟨ [], List.Perm.refl _, by simp ⟩
  | cons r rows =>
    have balance' : (rows.map pushOf : Multiset α) + {pushOf r} = (rows.map pullOf : Multiset α) + {pullOf r} := by
      simp only [List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add] at balance
      rw [add_comm, balance, add_comm]
    obtain ⟨ walk, rest, walk_perm, is_walk, rest_balance ⟩ := exists_walk pullOf pushOf rows _ _ balance'
    have length_lt : rest.length < n := by
      have := walk_perm.length_eq
      simp only [List.length_append, List.length_cons] at this h
      omega
    obtain ⟨ cycles, rest_perm, cycles_closed ⟩ := ih _ length_lt rest rest_balance rfl
    refine ⟨ (r :: walk) :: cycles, ?_, ?_ ⟩
    · simp only [List.flatten_cons, List.cons_append]
      exact List.Perm.cons r (walk_perm.trans (List.Perm.append_left walk rest_perm))
    · intro c c_mem
      rcases List.mem_cons.mp c_mem with rfl | c_mem
      · exact ⟨ r, walk, rfl, rfl, is_walk ⟩
      · exact cycles_closed c c_mem

end Walk

/-! ### The clock -/

/--
The clock a row pushes (§sec:clock), as an integer: one cycle on, `(t + 2^5 ℓ) mod 2^41` with `ℓ` the live bit 40
of `t`, plus bit 41 when one of the row's accesses is out of order. For `t < 2^41` the live bit is `2^40 ≤ t`.
-/
def nextClock (t : ℕ) (inOrder : Bool) : ℕ :=
  (t + if 2 ^ 40 ≤ t then 2 ^ 5 else 0) % 2 ^ 41 + if inOrder then 0 else 2 ^ 41

theorem nextClock_true (t : ℕ) : nextClock t true = (t + if 2 ^ 40 ≤ t then 2 ^ 5 else 0) % 2 ^ 41 := by
  simp [nextClock]

theorem nextClock_lt (t : ℕ) (inOrder : Bool) : nextClock t inOrder < 2 ^ 42 := by
  unfold nextClock
  generalize (t + if 2 ^ 40 ≤ t then 2 ^ 5 else 0) = u
  have := Nat.mod_lt u (show 2 ^ 41 > 0 by norm_num)
  cases inOrder <;> simp <;> omega

/--
A row's part in the state interaction (§sec:state): it pulls `⟨ST, pc, ts, 0⟩` and pushes `⟨ST, pc', ts', exit⟩`,
where `ts` names the integer `clock` and `ts'` the clock its clock circuit gives, `nextClock clock inOrder`.
-/
structure StateRow where
  pc : K
  clock : ℕ
  npc : K
  exit : K
  inOrder : Bool

namespace StateRow

/-- The state a row pulls. -/
noncomputable def pull (r : StateRow) : Tuple := tuple [sepST, r.pc, ofWord r.clock, 0]

/-- The state a row pushes. -/
noncomputable def push (r : StateRow) : Tuple :=
  tuple [sepST, r.npc, ofWord (nextClock r.clock r.inOrder), r.exit]

theorem pull_sep (r : StateRow) : r.pull[0] = sepST := by simp [pull, tuple_get]
theorem push_sep (r : StateRow) : r.push[0] = sepST := by simp [push, tuple_get]
theorem pull_clock (r : StateRow) : r.pull[2] = ofWord r.clock := by simp [pull, tuple_get]
theorem push_clock (r : StateRow) : r.push[2] = ofWord (nextClock r.clock r.inOrder) := by simp [push, tuple_get]

end StateRow

/-- The initial state `σ_initial = ⟨ST, pc_entry, 2^40 + 2^5, 0⟩`: the run starts live, on cycle 1. -/
noncomputable def initialState (pcEntry : K) : Tuple := tuple [sepST, pcEntry, ofWord (2 ^ 40 + 2 ^ 5), 0]

/-- The final state `σ_final = ⟨ST, pc_halt, ts_final, 1⟩`, `ts_final = 2^40 + 2^5 c` a live clock at slot 0. -/
noncomputable def finalState (pcHalt : K) (cycles : ℕ) : Tuple :=
  tuple [sepST, pcHalt, ofWord (2 ^ 40 + 2 ^ 5 * cycles), 1]

/-- The state flushes: every row pulls and pushes its state, the boundary pushes `σ_initial` and pulls `σ_final`. -/
noncomputable def stateFlushes (rows : List StateRow) (pcEntry pcHalt : K) (cycles : ℕ) : Flushes where
  pushes := initialState pcEntry :: rows.map StateRow.push
  pulls := finalState pcHalt cycles :: rows.map StateRow.pull

theorem coord_eq_of_eq {s t : Tuple} (h : s = t) (i : ℕ) (hi : i < 16) : s[i] = t[i] := by rw [h]

/-- Along a walk to `σ_final` from a clock without the live bit, the clock never changes, so it cannot get there. -/
theorem not_walk_of_dead (pcHalt : K) (cycles : ℕ) (cycles_lt : cycles < 2 ^ 35) :
    ∀ (w : List StateRow) (s : Tuple) (c : ℕ), c < 2 ^ 40 → s[2] = ofWord c →
      (∀ r ∈ w, r.clock < 2 ^ 41 ∧ r.inOrder = true) →
      ¬ IsWalk StateRow.pull StateRow.push s (finalState pcHalt cycles) w := by
  intro w
  induction w with
  | nil =>
    intro s c c_lt s_clock _ is_walk
    have := coord_eq_of_eq is_walk 2 (by norm_num)
    rw [s_clock] at this
    simp only [finalState, tuple_get] at this
    have := ofWord_injective (by omega) (by omega) this
    omega
  | cons r w ih =>
    intro s c c_lt s_clock rows_ok is_walk
    obtain ⟨ pull_eq, is_walk ⟩ := is_walk
    obtain ⟨ r_lt, r_ok ⟩ := rows_ok r (List.mem_cons_self ..)
    have clock_eq := coord_eq_of_eq pull_eq 2 (by norm_num)
    rw [StateRow.pull_clock, s_clock] at clock_eq
    have r_clock := ofWord_injective (by omega) (by omega) clock_eq
    apply ih r.push c c_lt _ (fun r' hr' => rows_ok r' (List.mem_cons_of_mem _ hr')) is_walk
    rw [StateRow.push_clock, r_ok, nextClock, r_clock]
    congr 1
    simp only [if_true, add_zero]
    rw [if_neg (by omega), add_zero, Nat.mod_eq_of_lt (by omega)]

/-- Along a walk to `σ_final` from the live clock of cycle `j`, the `i`-th row has the clock of cycle `j + i`. -/
theorem walk_clocks (pcHalt : K) (cycles : ℕ) (cycles_lt : cycles < 2 ^ 35) :
    ∀ (w : List StateRow) (s : Tuple) (j : ℕ), j < 2 ^ 35 → s[2] = ofWord (2 ^ 40 + 2 ^ 5 * j) →
      (∀ r ∈ w, r.clock < 2 ^ 41 ∧ r.inOrder = true) →
      IsWalk StateRow.pull StateRow.push s (finalState pcHalt cycles) w →
      (∀ i (hi : i < w.length), w[i].clock = 2 ^ 40 + 2 ^ 5 * (j + i)) ∧ j + w.length = cycles := by
  intro w
  induction w with
  | nil =>
    intro s j j_lt s_clock _ is_walk
    have := coord_eq_of_eq is_walk 2 (by norm_num)
    rw [s_clock] at this
    simp only [finalState, tuple_get] at this
    have := ofWord_injective (by omega) (by omega) this
    exact ⟨ fun i hi => absurd hi (Nat.not_lt_zero i), by simp; omega ⟩
  | cons r w ih =>
    intro s j j_lt s_clock rows_ok is_walk
    obtain ⟨ pull_eq, is_walk ⟩ := is_walk
    obtain ⟨ r_lt, r_ok ⟩ := rows_ok r (List.mem_cons_self ..)
    have rest_ok := fun r' hr' => rows_ok r' (List.mem_cons_of_mem r hr')
    have clock_eq := coord_eq_of_eq pull_eq 2 (by norm_num)
    rw [StateRow.pull_clock, s_clock] at clock_eq
    have r_clock := ofWord_injective (by omega) (by omega) clock_eq
    have push_clock := r.push_clock
    rw [r_ok, nextClock, r_clock, if_pos (by omega)] at push_clock
    simp only [if_true, add_zero] at push_clock
    by_cases wraps : j + 1 = 2 ^ 35
    · rw [show (2 ^ 40 + 2 ^ 5 * j + 2 ^ 5) % 2 ^ 41 = 0 by omega] at push_clock
      exact absurd is_walk (not_walk_of_dead pcHalt cycles cycles_lt w r.push 0 (by norm_num) push_clock rest_ok)
    rw [show (2 ^ 40 + 2 ^ 5 * j + 2 ^ 5) % 2 ^ 41 = 2 ^ 40 + 2 ^ 5 * (j + 1) by omega] at push_clock
    obtain ⟨ clocks, length_eq ⟩ := ih r.push (j + 1) (by omega) push_clock rest_ok is_walk
    refine ⟨ ?_, by simp only [List.length_cons]; omega ⟩
    intro i hi
    cases i with
    | zero => simp [r_clock]
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [clocks i (by simpa using hi)]
      ring

/--
Proposition `prop:walk` with Corollary `cor:clock` for the state interaction. Let every row pull a clock below `2^41`
and push the clock its clock circuit gives, the state tuples being carried only by the rows and the boundary.
If the bus balances, every row's accesses are in order, and the rows split into a walk `r_1, ..., r_L` from
`σ_initial` to `σ_final`, row `r_i` having the live clock `2^40 + 2^5 i` (so `L < 2^35` and these clocks are
distinct), and closed walks of rows whose clocks lack the live bit.
-/
theorem state_walk (rows : List StateRow) (pcEntry pcHalt : K) (cycles : ℕ) (cycles_lt : cycles < 2 ^ 35)
    (clock_lt : ∀ r ∈ rows, r.clock < 2 ^ 41)
    (rest : Flushes) (avoids : rest.Avoids fun t => t[0] = sepST)
    (balance : (rest ++ stateFlushes rows pcEntry pcHalt cycles).Balanced) :
    (∀ r ∈ rows, r.inOrder = true) ∧
      ∃ walk others : List StateRow, rows.Perm (walk ++ others) ∧
        IsWalk StateRow.pull StateRow.push (initialState pcEntry) (finalState pcHalt cycles) walk ∧
        walk.length + 1 = cycles ∧
        (∀ i (hi : i < walk.length), walk[i].clock = 2 ^ 40 + 2 ^ 5 * (i + 1)) ∧
        (∀ r ∈ others, r.clock < 2 ^ 40) ∧
        ∃ closed : List (List StateRow), others.Perm closed.flatten ∧
          ∀ c ∈ closed, ∃ r w, c = r :: w ∧ IsWalk StateRow.pull StateRow.push r.pull r.pull c := by
  classical
  -- the state tuples balance
  have sep_eq := Flushes.filter_eq_of_balanced balance fun t => t[0] = sepST
  simp only [Flushes.pushed_append, Flushes.pulled_append, Multiset.filter_add,
    Flushes.filter_pushed_of_avoids avoids, Flushes.filter_pulled_of_avoids avoids, zero_add] at sep_eq
  have states : ((rows.map StateRow.push : List Tuple) : Multiset Tuple) + {initialState pcEntry} =
      ((rows.map StateRow.pull : List Tuple) : Multiset Tuple) + {finalState pcHalt cycles} := by
    have pushed_eq : (stateFlushes rows pcEntry pcHalt cycles).pushed =
        ((initialState pcEntry :: rows.map StateRow.push : List Tuple) : Multiset Tuple) := by
      simp [Flushes.pushed, stateFlushes]
    have pulled_eq : (stateFlushes rows pcEntry pcHalt cycles).pulled =
        ((finalState pcHalt cycles :: rows.map StateRow.pull : List Tuple) : Multiset Tuple) := rfl
    rw [pushed_eq, pulled_eq, Multiset.filter_eq_self.mpr, Multiset.filter_eq_self.mpr] at sep_eq
    · rw [add_comm, Multiset.singleton_add, Multiset.cons_coe, sep_eq, ← Multiset.cons_coe,
        ← Multiset.singleton_add, add_comm]
    · intro t t_mem
      simp only [Multiset.mem_coe, List.mem_cons, List.mem_map] at t_mem
      rcases t_mem with rfl | ⟨ r, -, rfl ⟩
      · simp [finalState, tuple_get]
      · exact r.pull_sep
    · intro t t_mem
      simp only [Multiset.mem_coe, List.mem_cons, List.mem_map] at t_mem
      rcases t_mem with rfl | ⟨ r, -, rfl ⟩
      · simp [initialState, tuple_get]
      · exact r.push_sep
  -- a row out of order pushes a clock with bit 41 set, which nothing pulls
  have in_order : ∀ r ∈ rows, r.inOrder = true := by
    intro r r_mem
    by_contra not_in_order
    have mem : r.push ∈ ((rows.map StateRow.pull : List Tuple) : Multiset Tuple) + {finalState pcHalt cycles} := by
      rw [← states]
      exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr (List.mem_map_of_mem r_mem)))
    have next_ge : 2 ^ 41 ≤ nextClock r.clock r.inOrder := by
      simp only [nextClock, Bool.not_eq_true] at not_in_order ⊢
      rw [not_in_order]
      simp
    have next_lt := nextClock_lt r.clock r.inOrder
    rcases Multiset.mem_add.mp mem with mem | mem
    · obtain ⟨ r', r'_mem, eq ⟩ := List.mem_map.mp (Multiset.mem_coe.mp mem)
      have := coord_eq_of_eq eq 2 (by norm_num)
      rw [StateRow.pull_clock, StateRow.push_clock] at this
      have := ofWord_injective (by have := clock_lt r' r'_mem; omega) (by omega) this
      have := clock_lt r' r'_mem
      omega
    · have := coord_eq_of_eq (Multiset.mem_singleton.mp mem) 2 (by norm_num)
      rw [StateRow.push_clock] at this
      simp only [finalState, tuple_get] at this
      have := ofWord_injective (by omega) (by omega) this
      omega
  refine ⟨ in_order, ?_ ⟩
  obtain ⟨ walk, others, perm, is_walk, others_balance ⟩ :=
    exists_walk StateRow.pull StateRow.push rows _ _ states
  have rows_ok : ∀ r ∈ rows, r.clock < 2 ^ 41 ∧ r.inOrder = true := fun r hr => ⟨ clock_lt r hr, in_order r hr ⟩
  have walk_ok := fun r hr => rows_ok r (perm.mem_iff.mpr (List.mem_append_left others hr))
  have others_ok := fun r hr => rows_ok r (perm.mem_iff.mpr (List.mem_append_right walk hr))
  obtain ⟨ clocks, length_eq ⟩ := walk_clocks pcHalt cycles cycles_lt walk (initialState pcEntry) 1 (by norm_num)
    (by simp [initialState, tuple_get]) walk_ok is_walk
  refine ⟨ walk, others, perm, is_walk, by omega, fun i hi => by rw [clocks i hi]; ring, ?_,
    exists_closedWalks StateRow.pull StateRow.push others others_balance ⟩
  -- among the other rows, the clocks they push are the clocks they pull; a live one would have a live predecessor
  have clock_multiset : (others.map fun r => nextClock r.clock true : Multiset ℕ) = others.map StateRow.clock := by
    have := congrArg (Multiset.map fun t : Tuple => toWord t[2]) others_balance
    simp only [Multiset.map_coe, List.map_map] at this
    have push_eq : ∀ r ∈ others, ((fun t : Tuple => toWord t[2]) ∘ StateRow.push) r = nextClock r.clock true := by
      intro r hr
      simp only [Function.comp_apply, StateRow.push_clock, (others_ok r hr).2]
      exact toWord_ofWord _ (by have := nextClock_lt r.clock true; omega)
    have pull_eq : ∀ r ∈ others, ((fun t : Tuple => toWord t[2]) ∘ StateRow.pull) r = r.clock := by
      intro r hr
      simp only [Function.comp_apply, StateRow.pull_clock]
      exact toWord_ofWord _ (by have := (others_ok r hr).1; omega)
    rw [List.map_congr_left push_eq, List.map_congr_left pull_eq] at this
    exact this
  by_contra some_live
  push Not at some_live
  obtain ⟨ r0, r0_mem, r0_live ⟩ := some_live
  have exists_live : ∃ n, ∃ r ∈ others, 2 ^ 40 ≤ r.clock ∧ r.clock = n := ⟨ r0.clock, r0, r0_mem, r0_live, rfl ⟩
  obtain ⟨ rmin, rmin_mem, rmin_live, rmin_clock ⟩ := Nat.find_spec exists_live
  have rmin_mem' : rmin.clock ∈ (others.map StateRow.clock : Multiset ℕ) :=
    Multiset.mem_coe.mpr (List.mem_map_of_mem rmin_mem)
  rw [← clock_multiset] at rmin_mem'
  obtain ⟨ r', r'_mem, r'_next ⟩ := List.mem_map.mp (Multiset.mem_coe.mp rmin_mem')
  have r'_lt := (others_ok r' r'_mem).1
  have rmin_lt := (others_ok rmin rmin_mem).1
  rw [nextClock_true] at r'_next
  by_cases r'_live : 2 ^ 40 ≤ r'.clock
  · have := Nat.find_min' exists_live ⟨ r', r'_mem, r'_live, rfl ⟩
    rw [if_pos r'_live] at r'_next
    omega
  · rw [if_neg r'_live] at r'_next
    omega

end LeanVMCircuits.Bus
