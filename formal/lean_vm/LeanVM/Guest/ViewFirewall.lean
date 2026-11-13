import LeanVM.Guest.CheckView
import LeanVM.Guest.B2C.CplCheck
import LeanVM.Guest.B2C.ShareCheck
import LeanVM.Guest.B2C.ChainCheck

/-! **A function's checks over its view import no other function's data.** The checks of a
function's windows (`Pack/*/Checked*`, `Pack/*/Cplw*`) import its own code, core IR and
certificate, its callees' signatures, the jump table and the powers of `g` (`Data.Pows`), and the
checks' definitions (`CheckView`, `B2C.CplCheck`, `ShareCheck`, `ChainCheck`), so that an edit of another function rebuilds none
of them. This module fails to build if what an importer of those definitions sees (by Lake's rule:
the module and its public imports, transitively) reaches the guest's data. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let forbidden := [`LeanVM.Guest.Data, `Statement.Data, `LeanVM.Guest.Pack, `LeanVM.Guest.Glob,
    `LeanVM.Guest.CoreData, `LeanVM.Guest.FunctionTable, `LeanVM.Guest.Bytecode]
  let data : Std.HashMap Name ModuleData :=
    (env.header.moduleNames.zip env.header.moduleData).foldl (fun m (n, d) ↦ m.insert n d) {}
  for root in [`LeanVM.Guest.CheckView, `LeanVM.Guest.B2C.CplCheck, `LeanVM.Guest.B2C.ShareCheck,
      `LeanVM.Guest.B2C.ChainCheck] do
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
    let reached := seen.toList.filter fun m ↦ forbidden.any (·.isPrefixOf m)
    unless reached.isEmpty do
      throwError m!"`{root}` shows the guest's data {reached}: keep it out (see \
        `LeanVM/Guest/ViewFirewall.lean`)"
