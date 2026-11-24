import LeanVM.Guest.Pow
import LeanVM.Guest.Memory
import LeanVM.Guest.Memory.StaticRun
import LeanVM.Guest.CoreMode.HeapCWinM

/-! **Definitions about any program import no program's data.** The powers of `g` (`Pow`, over the
digit tables `Data.GTab`), the honest memory (`Memory`), the static checkers' walk by ranges
(`Memory.StaticRun`) and the heap check in windows (`CoreMode.HeapCWin`, `HeapCWinF`, `HeapCWinM`)
hold for every program, so that an edit of the guest rebuilds none of them nor the generated checks
that import only them and one function's data. Their guest-specific parts are apart: the powers
the guest names and its jump table (`Data.Pows`), `main`'s jump table cells (`Memory.TableCells`),
the families' steps (`Memory.StaticCut`). This module fails to build if what an importer of those
modules sees (by Lake's rule: the module and its public imports, transitively) reaches the guest's
data. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let forbidden := [`Statement.Data, `Statement.LeanVmGuest, `LeanVM.Guest.Pack, `LeanVM.Guest.Glob,
    `LeanVM.Guest.CoreData, `LeanVM.Guest.FunctionTable, `LeanVM.Guest.Bytecode]
  let allowed := [`LeanVM.Guest.Data.GTab]
  let data : Std.HashMap Name ModuleData :=
    (env.header.moduleNames.zip env.header.moduleData).foldl (fun m (n, d) ↦ m.insert n d) {}
  for root in [`LeanVM.Guest.Pow, `LeanVM.Guest.Memory, `LeanVM.Guest.Memory.StaticRun,
      `LeanVM.Guest.CoreMode.HeapCWinM] do
    let mut seen : NameSet := {}
    let mut todo := #[root]
    while !todo.isEmpty do
      let m := todo.back!
      todo := todo.pop
      if seen.contains m then continue
      seen := seen.insert m
      if let some d := data[m]? then
        for i in d.imports do
          if i.isExported || i.isMeta then todo := todo.push i.module
    let reached := seen.toList.filter fun m ↦ !allowed.contains m &&
      (forbidden.any (·.isPrefixOf m) || (`LeanVM.Guest.Data).isPrefixOf m)
    unless reached.isEmpty do
      throwError m!"`{root}` shows the guest's data {reached}: keep it out (see \
        `LeanVM/Guest/GenericFirewall.lean`)"
