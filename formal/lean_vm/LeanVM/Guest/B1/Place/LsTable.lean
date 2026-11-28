/-
  LeanVM.Guest.B1.Place.LsTable

  Every arm's `level_residual_slow` specializations are entries of `lrsTable`, by the kernel.
-/

module

public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.B1.Whir.NameNums

/-!
# The slow residuals in `lrsTable`

`lsIn_of`: at every non-final level `l` of every arm, `lrsTable` has an entry named
`osSlowName` of the level's shape (`lsIn_all`, by the kernel, by numbers: each entry is named by its numbers,
`lrs_names`).
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- An `lrsTable` entry's numbers: queries, prefix, tail rounds, vanishing offset. -/
def lrsKey (x : ℕ × ℕ × ℕ × ℕ × String × String × String) : List ℕ := [x.1, x.2.1, x.2.2.1, x.2.2.2.1]

set_option maxRecDepth 100000 in
theorem lrs_names : ∀ e ∈ lrsTable, e.1 = keyStr "level_residual_slow__L" (lrsKey e.2) := by
  decide +kernel

theorem osSlowName_eq (c : OsCfg) (lv : OsLv) :
    osSlowName c lv = keyStr "level_residual_slow__L" [lv.queries, lv.prefixLen, c.yrLog, lv.vanish] := rfl

/-- Every non-final level's `level_residual_slow` is an entry of `lrsTable` at the level's shape, by numbers. -/
def lsInB (c : OsCfg) : Bool :=
  (List.range c.yrLevel).all fun l ↦ lrsTable.any fun e ↦
    lrsKey e.2 == [(c.levels.getD l default).queries, (c.levels.getD l default).prefixLen, c.yrLog,
      (c.levels.getD l default).vanish]

/-- Every arm, every rate, by the kernel. -/
theorem lsIn_all : ∀ m < ligNSizes, ∀ ri < 4, lsInB (osCfgR m ri) = true := by decide +kernel

theorem lsIn_of {c : OsCfg} (h : lsInB c = true) {l : ℕ} (hl : l < c.yrLevel) :
    ∃ e ∈ lrsTable, e.1 = osSlowName c (c.levels.getD l default) ∧
      e.2.1 = (c.levels.getD l default).queries ∧ e.2.2.1 = (c.levels.getD l default).prefixLen ∧
      e.2.2.2.1 = c.yrLog ∧ e.2.2.2.2.1 = (c.levels.getD l default).vanish := by
  obtain ⟨e, he, hb⟩ := List.any_eq_true.mp (List.all_eq_true.mp h l (List.mem_range.mpr hl))
  have hk := beq_iff_eq.mp hb
  simp only [lrsKey, List.cons.injEq, and_true] at hk
  obtain ⟨h1, h2, h3, h4⟩ := hk
  refine ⟨e, he, ?_, h1, h2, h3, h4⟩
  rw [lrs_names e he, osSlowName_eq, lrsKey, h1, h2, h3, h4]

end
end LeanVM.Guest.B1.Whir
