import Lean

/-!
# Which imports a module needs

`lake env lean --run ../tools/NeededImports.lean <Module> [--consts]`, from a project's directory
after building `<Module>`: the modules of the repository's projects that `<Module>` imports, those
its declarations need, and the needed modules that import unneeded ones (the modules to split).

A declaration needs the constants of its type and, for a definition, of its value; a theorem of
the repository also needs those of its proof (it must be elaborated where it is declared), a
theorem of a dependency only its statement. A module is needed when it declares a needed
constant. Tactics, notation and attributes are not constants: an import that provides only those
is reported as unneeded, and the build says otherwise.

A module is rebuilt whenever a module it imports changes its interface (any module, for a module
outside the module system), so a module that is slow to build, such as one of kernel-checked
certificates, should import what it needs alone. `--consts` also prints every needed constant with
its module (`CONST <module> <constant>`), to find what to move when splitting a module.
-/

open Lean

/-- The packages the repository depends on: their modules are not the repository's. -/
def external : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `VCVio, `ToMathlib, `CompPoly,
    `ArkLib, `Clean, `PolyFun, `Cslib, `Plausible, `ProofWidgets, `ImportGraph, `LeanSearchClient]

def isOurs (m : Name) : Bool := !(external.contains m.getRoot)

def main (args : List String) : IO UInt32 := do
  let some modArg := args.find? (!·.startsWith "--")
    | IO.eprintln "usage: lake env lean --run NeededImports.lean <Module> [--consts]"; return 2
  let modName := modArg.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := modName, importAll := true }] {} (loadExts := false)
  let names := env.header.moduleNames
  let modOf (c : Name) : Option Name := (env.getModuleIdxFor? c).map (names[·.toNat]!)
  let some self := env.getModuleIdx? modName | IO.eprintln s!"{modName} is not built"; return 1
  -- the closure of the module's own constants
  let mut todo : List Name := env.constants.map₁.toList.filterMap fun (c, _) ↦
    if env.getModuleIdxFor? c == some self then some c else none
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let mut used := ci.type.getUsedConstants
    match ci with
    | .defnInfo d => used := used ++ d.value.getUsedConstants
    | .opaqueInfo d => used := used ++ d.value.getUsedConstants
    | .thmInfo d => if (modOf c).all isOurs then used := used ++ d.value.getUsedConstants
    | .inductInfo d => used := used ++ d.ctors.toArray
    | .ctorInfo d => used := used.push d.induct
    | .recInfo d => used := used.push d.getMajorInduct
    | _ => pure ()
    for u in used do
      if !seen.contains u then todo := u :: todo
  let mut needed : NameSet := {}
  for c in seen do
    if let some m := modOf c then needed := needed.insert m
  if args.contains "--consts" then
    for c in seen do
      if let some m := modOf c then
        if isOurs m && m != modName then IO.println s!"CONST {m} {c}"
  -- the repository's modules imported, needed, and to split
  let ours := names.filter fun m ↦ isOurs m && m != modName
  let unneeded := ours.filter (!needed.contains ·)
  IO.println s!"{modName} imports {ours.size} modules of the repository and needs {ours.size - unneeded.size}"
  unless unneeded.isEmpty do
    IO.println s!"not needed ({unneeded.size}):"
    for m in unneeded.qsort (·.toString < ·.toString) do IO.println s!"  {m}"
  let mut split : Array String := #[]
  for i in [:names.size] do
    let m := names[i]!
    if !isOurs m || m == modName || !needed.contains m then continue
    let extra := env.header.moduleData[i]!.imports.filterMap fun imp ↦
      if isOurs imp.module && !needed.contains imp.module then some imp.module else none
    unless extra.isEmpty do
      split := split.push s!"  {m}: imports {extra.toList}"
  unless split.isEmpty do
    IO.println "needed modules importing unneeded ones (split them):"
    for s in split.qsort (· < ·) do IO.println s
  return 0
