/-
  LeanVM.Guest.CoreData

  The core IR of the aggregation guest as data, its functions by index and by name, and their
  pairing with the compiled functions.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.CoreFind
public import LeanVM.Guest.Data.Names
public import LeanVM.Guest.Renumber
public import Statement.Data.Bytecode
public import LeanVM.Guest.Code

/-!
# The guest's core IR

`coreProgram` is `Expand.expandProgram Data.guest` with every function renumbered
(`Fn.renumber`: its values are `V.n 0`, `V.n 1`, ..., the parameters first), written out by
`lake exe guest-core` (one definition `Fn.<key>.core` per function keyed by its stable name, in
its pack `Pack/P<k>/Core.lean` or, when long, its own `Pack/<key>/Core.lean`, listed in the
compiler's order by `Data/Core.lean`, which keeps `Data.core{j}` as an abbreviation of function
`j`), so that no proof evaluates the expansion; `lake exe guest-core --values f` prints the
expansion's name of each value of `f`.
`tests/LeanVMTests/Guest/CoreDataCheck.lean` reads the definitions back and compares them with the
renumbered expansion. Renumbering changes no relation (`Program.rel_map_renumber`). The data is
noncomputable: it is a term for the kernel and the proofs, never compiled.

* `coreProgram[j]? = some Data.core{j}` is `rfl` (under a `maxRecDepth` above the default for a
  large `j`), unfolding the function list only;
* `coreProgram.find? name = some f` is `Program.find?_of_indexOf?` (`CoreFind.lean`), from
  `coreProgram[j]? = some f` and `coreProgram.indexOf? name = some j`; deciding the latter compares
  `name` with the names before it in the kernel, slowly, so the proofs use `coreProgram_find?_at`
  (`B1/Common/Find.lean`) instead, from `coreProgram[j]? = some f` and the names' distinctness
  (`CoreNames.lean`);
* `name_eq_compiled`: function `j` has the name of compiled function `j + 1` of
  `Data.functions`, after `__jump_tables`.
-/

namespace LeanVM.Guest

open Core

@[expose] public section

/-- The guest's core IR, `main` first. -/
noncomputable def coreProgram : Program := Data.coreFunctions

theorem coreProgram_length : coreProgram.length = core_count% := by decide +kernel

/-- Function `j` has the name of compiled function `j + 1`, after `__jump_tables`. -/
theorem names_eq : coreProgram.map Fn.name = Data.functions.tail.map CompiledFunction.name := by
  decide +kernel

theorem name_eq_compiled {j : Nat} {f : Fn} {c : CompiledFunction} (hf : coreProgram[j]? = some f)
    (hc : Data.functions[j + 1]? = some c) : f.name = c.name := by
  have h := congrArg (·[j]?) names_eq
  simp only [List.getElem?_map, hf, List.getElem?_tail, hc, Option.map_some] at h
  exact Option.some.inj h

end
end LeanVM.Guest
