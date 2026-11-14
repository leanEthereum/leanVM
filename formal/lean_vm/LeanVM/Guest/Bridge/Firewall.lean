import LeanVM.Guest.Bridge.Defs
import LeanVM.Guest.Bridge.AlignDefs

/-! **The hint bridge's certificates read the bridge's definitions, the guest's code and their own data
alone.** Each `Bridge/PrefixOk/*` and `Bridge/Align/*` module imports the definitions (`Bridge.Defs`, `Bridge.AlignDefs`, which adds the executor's power table and tries), the powers of `g` and the jump table (`Data.Pows`, `Align` only), the advice by function
(`Data.AdviceHints`), its pack's code and certificates (`Bundle`) and its functions' core IR (`Core`). This
module fails to build if the definitions reach the bridge's proofs, B1's, the protocol's, the schemes' or
the honest prover beyond its executor (`Statement.Prover.Execute`, whose `Hint` the bridge reads), as
`B2C/CertFirewall.lean` does for the other certificates, or if what an importer of the definitions sees
reaches the guest's data, as `ViewFirewall.lean` does. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let forbidden := [`LeanVM.Guest.Bridge.Prefix, `LeanVM.Guest.Bridge.Cells, `LeanVM.Guest.Bridge.Track,
    `LeanVM.Guest.Bridge.PrefixTrack, `LeanVM.Guest.Bridge.PrefixRun, `LeanVM.Guest.Bridge.RefTrace,
    `LeanVM.Guest.Bridge.RefHonest, `LeanVM.Guest.Bridge.TrackHonest, `LeanVM.Guest.Mode,
    `LeanVM.Guest.B1, `LeanVM.Protocol, `LeanVM.Facts.Verifier, `LeanVM.Guest.Logic,
    `LeanVM.Guest.Bytecode, `LeanVM.Prover, `LeanXmss, `Sphincs, `LeanDa, `Common, `Statement.LeanVm,
    `Statement.LeanVmGuest, `Statement.LeanXmss, `Statement.LeanSphincs, `Statement.LeanDa,
    `Statement.Fast.Schemes, `Statement.CostMachine, `Statement.Theorems, `Statement.Corollaries]
  let reached := env.header.moduleNames.filter fun m ↦
    forbidden.any (·.isPrefixOf m) ||
      ((`Statement.Prover).isPrefixOf m && m != `Statement.Prover.Execute)
  unless reached.isEmpty do
    throwError m!"the hint bridge's certificates import {reached.toList}: keep the definitions in \
      modules that do not (see `LeanVM/Guest/Bridge/Firewall.lean`)"
  let data : Std.HashMap Name ModuleData :=
    (env.header.moduleNames.zip env.header.moduleData).foldl (fun m (n, d) ↦ m.insert n d) {}
  let guestData := [`LeanVM.Guest.Data, `Statement.Data, `LeanVM.Guest.Pack, `LeanVM.Guest.Glob,
    `LeanVM.Guest.CoreData, `LeanVM.Guest.FunctionTable]
  let mut seen : NameSet := {}
  let mut todo := #[`LeanVM.Guest.Bridge.Defs, `LeanVM.Guest.Bridge.AlignDefs]
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
    throwError m!"`LeanVM.Guest.Bridge.Defs` or `AlignDefs` shows the guest's data {shown}: keep it out (see \
      `LeanVM/Guest/Bridge/Firewall.lean`)"
