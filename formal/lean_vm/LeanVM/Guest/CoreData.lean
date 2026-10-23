/-
  LeanVM.Guest.CoreData

  The core IR of the aggregation guest as data, its functions by index and by name, and their
  pairing with the compiled functions.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.Data.Bytecode

/-!
# The guest's core IR

`coreProgram` is `Expand.expandProgram Data.guest` with every function renumbered
(`Fn.renumber`: its values are `V.n 0`, `V.n 1`, ..., the parameters first), written out by
`lake exe guest-core` (`Data/Core*`, one definition `Data.core{j}` per function, in the
compiler's order), so that no proof evaluates the expansion; `lake exe guest-core --values f`
prints the expansion's name of each value of `f`. `tests/LeanVMTests/Guest/CoreData.lean` reads
the definitions back and compares them with the renumbered expansion. Renumbering changes no
relation (`Program.rel_map_renumber`). The data is noncomputable: it is a term for the kernel and
the proofs, never compiled.

* `coreProgram[j]? = some Data.core{j}` is `rfl` (under a `maxRecDepth` above the default for a
  large `j`), unfolding the function list only;
* `coreProgram.find? name = some f` is `Program.find?_of_indexOf?`, from `coreProgram[j]? = some f`
  and `coreProgram.indexOf? name = some j` by `decide +kernel`, which compares `name` with the
  names before it;
* `name_eq_compiled`: function `j` has the name of compiled function `j + 1` of
  `Data.functions`, after `__jump_tables`.
-/

namespace LeanVM.Guest

open Core

@[expose] public section

/-- The guest's core IR, `main` first. -/
noncomputable def coreProgram : Program := Data.coreFunctions

/-- The index of the first function of a name. -/
def Core.Program.indexOf? (P : Program) (n : String) : Option Nat := P.findIdx? (·.name == n)

/-- A function found by its index. -/
theorem Core.Program.find?_of_indexOf? {n : String} :
    ∀ {P : Program} {j : Nat} {f : Fn}, P.indexOf? n = some j → P[j]? = some f →
      P.find? n = some f
  | [], _, _, h, _ => by simp [Program.indexOf?] at h
  | g :: P, j, f, h, hj => by
      unfold Program.indexOf? at h
      unfold Program.find?
      by_cases hg : (g.name == n) = true
      · simp only [List.findIdx?_cons, hg, ↓reduceIte, Option.some.injEq] at h
        subst h
        simpa [List.find?_cons, hg] using hj
      · simp only [List.findIdx?_cons, hg] at h
        obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [List.getElem?_cons_succ] at hj
        simpa [List.find?_cons, hg, Program.find?] using find?_of_indexOf? hk hj

theorem coreProgram_length : coreProgram.length = 1043 := by decide +kernel

/-- Function `j` has the name of compiled function `j + 1`, after `__jump_tables`. -/
theorem names_eq : coreProgram.map Fn.name = Data.functions.tail.map CompiledFn.name := by
  decide +kernel

theorem name_eq_compiled {j : Nat} {f : Fn} {c : CompiledFn} (hf : coreProgram[j]? = some f)
    (hc : Data.functions[j + 1]? = some c) : f.name = c.name := by
  have h := congrArg (·[j]?) names_eq
  simp only [List.getElem?_map, hf, List.getElem?_tail, hc, Option.map_some] at h
  exact Option.some.inj h

end
end LeanVM.Guest
