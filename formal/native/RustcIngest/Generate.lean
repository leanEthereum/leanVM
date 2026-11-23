module

public meta import RustcIngest.Core

namespace Ingest

open Lean

public meta def writeWrappers {I C : Type} [ToExpr I] [ToExpr C] [BEq I] [BEq C]
    (base : Arch I C) (target adapter command : String) (args : List String) : IO UInt32 := do
  let [out] := args | throw <| IO.userError "expected an output directory"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := base.syntaxModule.toName }] {}
  for vm in [false, true] do
    let ns := if vm then base.ns.replace "Rustc" "RustcVm" else base.ns
    let arch := { base with ns, labels := !vm }
    let names ← if vm then readNames "rustc/ingest/vm-names.txt" else pure {}
    let mut schemes := #[]
    for scheme in (if vm then #["vm"] else #["xmss", "sphincs"]) do
      let dir := if vm then "rustc/vm/asm" else "rustc/asm"
      let file := if vm then "vm" else "signatures"
      let assembly ← IO.FS.readFile s!"{dir}/{file}-{target}.s"
      schemes := schemes.push (← ingestScheme arch env names scheme assembly)
    for (path, source) in ← emit arch env schemes do
      let imports := (source.splitOn "\n").filter (·.startsWith "public import ")
      let wrapper := "module\n\n" ++ String.join (imports.map (· ++ "\n")) ++
        s!"public meta import RustcIngest.{adapter}\n\n{command} {ns.quote} {path.quote}\n"
      let file : System.FilePath := out / path
      IO.FS.createDirAll file.parent.get!
      IO.FS.writeFile file wrapper
  return 0

end Ingest
