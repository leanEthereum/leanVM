/-
  LeanVM.Guest.Memory.GuestIdx

  The index of a guest function by name, for the generated certificate families
  (`Memory/GuestWords`, `Memory/GuestCnt*`).
-/

module

public import LeanVM.Guest.CoreNames
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core

@[expose] public section

/-- The index of a function of the guest by name. -/
noncomputable def coreIdx (g : String) : ℕ := (coreProgram.map (·.name)).idxOf g

theorem coreIdx_getElem {j : ℕ} (h : j < coreProgram.length) : coreIdx coreProgram[j].name = j := by
  have h' : j < (coreProgram.map (·.name)).length := by rwa [List.length_map]
  have := coreProgram_names_nodup.idxOf_getElem j h'
  rwa [List.getElem_map] at this

theorem coreIdx_of_name {j : ℕ} {g : String} (h : (coreProgram[j]?).map Fn.name = some g) :
    coreIdx g = j := by
  rcases hj : coreProgram[j]? with _ | fn
  · rw [hj] at h; exact absurd h (by simp)
  · rw [hj] at h
    obtain ⟨hlt, hfn⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h, ← hfn, coreIdx_getElem hlt]

end
end LeanVM.Guest
