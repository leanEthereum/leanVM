/-
  LeanVM.Guest.B1.Place.LsTable

  Every arm's `level_residual_slow` specializations are entries of `lrsTable`, by the kernel.
-/

module

public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Whir.Template

/-!
# The slow residuals in `lrsTable`

`lsIn_of`: at every non-final level `l` of every arm, `lrsTable` has an entry named
`osSlowName` of the level's shape (`lsIn_all`, by the kernel).
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- Every non-final level's `level_residual_slow` is an entry of `lrsTable` at the level's shape. -/
def lsInB (c : OsCfg) : Bool :=
  (List.range c.yrLevel).all fun l ↦ lrsTable.any fun e ↦
    e.1 == osSlowName c (c.levels.getD l default) && e.2.1 == (c.levels.getD l default).queries &&
      e.2.2.1 == (c.levels.getD l default).prefixLen && e.2.2.2.1 == c.yrLog &&
      e.2.2.2.2.1 == (c.levels.getD l default).vanish

/-- Every arm, every rate, by the kernel. -/
theorem lsIn_all : ∀ m < 11, ∀ ri < 4, lsInB (osCfgR m ri) = true := by decide +kernel

theorem lsIn_of {c : OsCfg} (h : lsInB c = true) {l : ℕ} (hl : l < c.yrLevel) :
    ∃ e ∈ lrsTable, e.1 = osSlowName c (c.levels.getD l default) ∧
      e.2.1 = (c.levels.getD l default).queries ∧ e.2.2.1 = (c.levels.getD l default).prefixLen ∧
      e.2.2.2.1 = c.yrLog ∧ e.2.2.2.2.1 = (c.levels.getD l default).vanish := by
  obtain ⟨e, he, hb⟩ := List.any_eq_true.mp (List.all_eq_true.mp h l (List.mem_range.mpr hl))
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hb
  exact ⟨e, he, h1, h2, h3, h4, h5⟩

end
end LeanVM.Guest.B1.Whir
