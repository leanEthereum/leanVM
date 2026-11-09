/-
  LeanVM.Guest.NameIndex

  The index of a guest function by its name.
-/

module

public import LeanVM.Guest.CoreNames

/-!
# Functions by name

A guest function's **index** is one past its position in `coreProgram` (`main` is `1`), the index
the certificates (`certOf`, `certByName`), the replayed frame map's entry table
(`Located/ReplayFast.lean`) and the decoder's numbered frames (`Fast/FunctionNames.lean`) use.
`nameIndex f` is the index of the first function named `f`; the names being distinct
(`coreProgram_names_nodup`), the function at position `i` is the first of its name
(`findIdx_name_of_nodup`). This module imports the names alone, so the kernel-checked tables of
the decoder's readers that name functions (`Fast/WhirTablesCheck.lean`) import neither the
certificates nor the checker.
-/

namespace LeanVM.Guest

@[expose] public section

/-- **The index of the function named `f`**: one past the first of `coreProgram` named `f`
(`main` is `1`, `coreProgram.length + 1` for no function). -/
noncomputable def nameIndex (f : String) : ℕ := coreProgram.findIdx (fun g ↦ g.name == f) + 1

theorem findIdx_name_of_nodup :
    ∀ {l : List Core.Fn}, (l.map (·.name)).Nodup → ∀ {i : ℕ} (h : i < l.length),
      l.findIdx (fun g ↦ g.name == l[i].name) = i
  | [], _, _, h => absurd h (by simp)
  | g :: l, hn, i, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    cases i with
    | zero => simp [List.findIdx_cons]
    | succ i =>
      have hi : i < l.length := by simpa using h
      have hne : (g.name == l[i].name) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        exact hn.1 (he ▸ List.mem_map_of_mem (List.getElem_mem hi))
      rw [List.findIdx_cons, List.getElem_cons_succ, hne, findIdx_name_of_nodup hn.2 hi]
      rfl

end
end LeanVM.Guest
