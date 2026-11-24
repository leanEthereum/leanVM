/-
  LeanVM.Guest.B1.Place.KindPre

  `open_stacked`'s named callees start as no level helper's specialization.
-/

module

public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Place.NamePre

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **The named callees start as no `level_positions`, `level_residual` or `level_queries`
specialization**, by the kernel over `osKindTable`. -/
theorem osKindTable_pre : ∀ e ∈ osKindTable, ¬ HasPre "level_positions__L" e.1 ∧
    ¬ HasPre "level_residual__L" e.1 ∧ ¬ HasPre "level_queries__L" e.1 := by
  decide +kernel

theorem osKindOf_pre {f : String} {K : OsKind} (h : osKindOf f = some K) : ¬ HasPre "level_positions__L" f ∧
    ¬ HasPre "level_residual__L" f ∧ ¬ HasPre "level_queries__L" f :=
  osKindTable_pre _ (os_mem_of_lookup osKindTable h)

end
end LeanVM.Guest.B1
