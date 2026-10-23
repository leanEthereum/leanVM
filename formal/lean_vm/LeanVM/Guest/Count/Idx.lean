/-
  LeanVM.Guest.Count.Idx

  The index of a guest function by name, for the certificates counting instructions.
-/

module

public import LeanVM.Guest.CoreNames
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core

@[expose] public section

/-- The index of a function of the guest by name. -/
noncomputable def kcIdx (g : String) : ℕ := (coreProgram.map (·.name)).idxOf g

theorem kcIdx_getElem {j : ℕ} (h : j < coreProgram.length) : kcIdx coreProgram[j].name = j := by
  have h' : j < (coreProgram.map (·.name)).length := by rwa [List.length_map]
  have := coreProgram_names_nodup.idxOf_getElem j h'
  rwa [List.getElem_map] at this

theorem kcIdx_of_name {j : ℕ} {g : String} (h : (coreProgram[j]?).map Fn.name = some g) :
    kcIdx g = j := by
  rcases hj : coreProgram[j]? with _ | fn
  · rw [hj] at h; exact absurd h (by simp)
  · rw [hj] at h
    obtain ⟨hlt, hfn⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h, ← hfn, kcIdx_getElem hlt]

end
end LeanVM.Guest
