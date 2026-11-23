/-
  LeanVM.Guest.CoreMode.Fn.opening_queries.Sound

  `opening_queries`'s own routing facts, sound (`CoreMode/FnReg.lean`): its exponent facts, carried down from its callers
  (`EndExec.expOk_of_carry`).
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResExpC
public import LeanVM.Guest.CoreMode.Fn.opening_queries.Data

namespace LeanVM.Guest.CoreMode.Own.opening_queries

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

public section

theorem expFacts_eq : expFacts = expCarry.map fun c ↦ (c.1, c.2.1, none, c.2.2.2) := by
  simp [expFacts, expCarry, List.map_append, List.map_map, Function.comp_def]

/-- **Its exponent facts** (`expOk_of_carry`). -/
theorem expFacts_ok : ∀ c ∈ expFacts, ExpOk c := by
  intro c hc
  rw [expFacts_eq] at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  exact expOk_of_carry (FnReg.expCarry_of_opening_queries _ hc')

end

end LeanVM.Guest.CoreMode.Own.opening_queries
