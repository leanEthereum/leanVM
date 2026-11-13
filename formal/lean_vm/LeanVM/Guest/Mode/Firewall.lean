import LeanVM.Guest.Mode.Abs
import LeanVM.Guest.Mode.Win
import LeanVM.Guest.Data.Pows

/-! **The mode walk's certificates read the walk, the guest's code and their view alone.** Each
`Pack/*/Mode*` module imports the walk (`Mode.Abs`, by windows `Mode.Win`), the powers of `g` and the
jump table (`Data.Pows`), its pack's code (`Bundle`) and its callees' signatures (`ModeSig`). This module fails
to build if the walk or `Data.Pows` reach the walk's soundness proofs, B1's, the protocol's, the
schemes' or the honest prover beyond its executor (`Statement.Prover.Execute`, whose `Op` and `Hint`
the walk reads), as `B2C/CertFirewall.lean` does for the other certificates, or if what an importer of
the walk sees reaches the guest's data, as `ViewFirewall.lean` does. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let forbidden := [`LeanVM.Guest.Mode.Sound, `LeanVM.Guest.B1, `LeanVM.Protocol,
    `LeanVM.Facts.Verifier, `LeanVM.Guest.Logic, `LeanVM.Guest.Bytecode, `LeanXmss, `Sphincs, `LeanDa,
    `Common, `Statement.LeanVm, `Statement.LeanVmGuest, `Statement.LeanXmss, `Statement.LeanSphincs,
    `Statement.LeanDa, `Statement.Fast.Schemes, `Statement.CostMachine, `Statement.Theorems,
    `Statement.Corollaries]
  let reached := env.header.moduleNames.filter fun m ↦
    forbidden.any (·.isPrefixOf m) ||
      ((`Statement.Prover).isPrefixOf m && m != `Statement.Prover.Execute)
  unless reached.isEmpty do
    throwError m!"the mode walk's certificates import {reached.toList}: keep the walk in modules \
      that do not (see `LeanVM/Guest/Mode/Firewall.lean`)"
  let data : Std.HashMap Name ModuleData :=
    (env.header.moduleNames.zip env.header.moduleData).foldl (fun m (n, d) ↦ m.insert n d) {}
  let guestData := [`LeanVM.Guest.Data, `Statement.Data, `LeanVM.Guest.Pack, `LeanVM.Guest.Glob,
    `LeanVM.Guest.CoreData, `LeanVM.Guest.FunctionTable]
  let mut seen : NameSet := {}
  let mut todo := #[`LeanVM.Guest.Mode.Abs, `LeanVM.Guest.Mode.Win]
  while !todo.isEmpty do
    let m := todo.back!
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if let some d := data[m]? then
      for i in d.imports do
        if i.isExported || i.isMeta then todo := todo.push i.module
  let shown := seen.toList.filter fun m ↦ guestData.any (·.isPrefixOf m)
  unless shown.isEmpty do
    throwError m!"`LeanVM.Guest.Mode.Abs` or `Win` shows the guest's data {shown}: keep it out (see \
      `LeanVM/Guest/Mode/Firewall.lean`)"
