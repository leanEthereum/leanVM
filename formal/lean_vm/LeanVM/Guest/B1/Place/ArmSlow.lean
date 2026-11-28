/-
  LeanVM.Guest.B1.Place.ArmSlow

  The facts of `open_stacked`'s dispatches into `level_residual_slow`: their numbers by kernel evaluation, their names
  by the family's prefix.
-/

module

public import LeanVM.Guest.B1.Place.ArmData
public import LeanVM.Guest.B1.Place.ArmXT
public import LeanVM.Guest.B1.Place.ArmMuteDef

/-!
# The slow residuals' facts

`SlowFacts c`: the tail challenges within `yrLogCap`, and at each non-final level its fold
challenges within `fold_challenges` and its `level_residual_slow` neither `armExactS` nor a name of
`lqTable`. `armSlow_ok`: every arm at every rate, the numbers from `slowNumB` by kernel evaluation, the names for
every specialization at once: each is `slowPre ++ s` (`osSlowName_eq`), and no name `armExactS` or `lqNameB` accepts
starts with `slowPre` (`noSlowPre`, one kernel pass over the two tables' bytes), so the kernel never builds a name.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- The facts of an arm's dispatches into `level_residual_slow`. -/
abbrev SlowFacts (c : OsCfg) : Prop :=
  c.yrLog ≤ yrLogCap ∧ ∀ l < c.yrLevel, (osLvA c l).resFoldOff + (osLvA c l).prefixLen ≤ c.nFolds ∧
    armExactS (osSlowName c (osLvA c l)) = false ∧ lqNameB (osSlowName c (osLvA c l)) = false

/-- The prefix of every `level_residual_slow` specialization's name. -/
def slowPre : String := "level_residual_slow__L"

theorem osSlowName_eq (c : OsCfg) (lv : OsLv) :
    osSlowName c lv = slowPre ++ (natStr lv.queries ++ "_L" ++ natStr lv.prefixLen ++ "_L" ++ natStr c.yrLog ++
      "_L" ++ natStr lv.vanish) := by
  simp only [osSlowName, slowPre, String.append_assoc]

/-- The names `armExactS` and `lqNameB` read. -/
def armNames : List String := ("is_zero" :: lpTable.map (·.1)) ++ lqTable.map (·.1)

/-- A string's UTF-8 bytes, as a list: the kernel reads a literal's bytes far faster than its characters. -/
def strBytes (s : String) : List UInt8 := s.toByteArray.data.toList

theorem strBytes_append (s t : String) : strBytes (s ++ t) = strBytes s ++ strBytes t := by
  simp only [strBytes, String.toByteArray_append, ByteArray.data_append, Array.toList_append]

/-- No name of `armNames` starts with `slowPre`'s bytes. -/
theorem noSlowPre : armNames.all (fun n ↦ !(strBytes slowPre).isPrefixOf (strBytes n)) = true := by decide +kernel

theorem slowPre_ne {n : String} (hn : n ∈ armNames) (s : String) : slowPre ++ s ≠ n := by
  rintro rfl
  have h := List.all_eq_true.mp noSlowPre _ hn
  rw [strBytes_append, List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)] at h
  exact absurd h (by decide)

/-- **No `level_residual_slow` is `armExactS`.** -/
theorem armExactS_slowPre (s : String) : armExactS (slowPre ++ s) = false := by
  rw [armExactS, Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.any_eq_false]
  exact ⟨slowPre_ne (by simp [armNames]) s, fun e he h ↦ slowPre_ne
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, he, rfl⟩))) s (beq_iff_eq.mp h).symm⟩

/-- **No `level_residual_slow` is a name of `lqTable`.** -/
theorem lqNameB_slowPre (s : String) : lqNameB (slowPre ++ s) = false := by
  rw [lqNameB, List.any_eq_false]
  exact fun e he h ↦ slowPre_ne (List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)) s (beq_iff_eq.mp h).symm

/-- The numbers of `SlowFacts`, checked. -/
def slowNumB (c : OsCfg) : Bool :=
  decide (c.yrLog ≤ yrLogCap) && (List.range c.yrLevel).all fun l ↦
    decide ((osLvA c l).resFoldOff + (osLvA c l).prefixLen ≤ c.nFolds)

/-- Every arm, every rate, by the kernel. -/
theorem slowNum_all : ∀ m < 11, ∀ ri < 4, slowNumB (osCfgR m ri) = true := by decide +kernel

/-- **Every arm's dispatches into `level_residual_slow` have their facts at every rate.** -/
theorem armSlow_ok {m ri : ℕ} (hm : m < 11) (hri : ri < 4) : SlowFacts (osCfgR m ri) := by
  have h := slowNum_all m hm ri hri
  simp only [slowNumB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, fun l hl ↦ ⟨h.2 l hl, osSlowName_eq _ _ ▸ armExactS_slowPre _, osSlowName_eq _ _ ▸ lqNameB_slowPre _⟩⟩

end
end LeanVM.Guest.B1.Arm
