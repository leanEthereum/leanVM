import Lean.Replay

/-!
# Every declaration of a module, checked again by the kernel

`lake env lean --run ../tools/KernelCheck.lean MODULE...`, from a project's directory after building it: each module's
declarations, read from its `.olean` (its private part included), replayed by the kernel into the environment of the
module's imports, as the toolchain's `leanchecker` does (`replayFromImports`), but for exactly the modules named
(`leanchecker MODULE` also checks every module under `MODULE`), and with the imports at the level the module's build
saw. A declaration that was added without the kernel (`debug.skipKernelTC`, which `#print axioms` cannot see, or
meta code adding it) fails here. Prints `ok MODULE` for each module checked; stops at the first failure.
`tools/kernel-check.py` runs it over every module.
-/

open Lean

unsafe def replayModule (module : Name) : IO Unit := do
  let file ← findOLean module
  unless ← file.pathExists do
    throw <| IO.userError s!"{module}: no .olean"
  let mut files := #[file]
  for level in [OLeanLevel.server, .private] do
    let part := level.adjustFileName file
    if ← part.pathExists then files := files.push part
  let parts ← readModuleDataParts files
  let some (mod, _) := parts[0]? | throw <| IO.userError s!"{module}: no module data"
  let some (last, _) := parts.back? | throw <| IO.userError s!"{module}: no module data"
  -- The imports at the level the module was built against (`processHeaderCore`): a `module` sees what its imports
  -- export, and what they keep private only through `import all`. With every private part loaded, as
  -- `leanchecker` does, the kernel unfolds definitions the build could not, and a check the build did in seconds
  -- can run out of memory.
  let level := if mod.isModule then OLeanLevel.exported else .private
  let (_, s) ← importModulesCore mod.imports (globalLevel := level) |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (level := level)
  let mut consts : Std.HashMap Name ConstantInfo := {}
  for name in last.constNames, ci in last.constants do
    consts := consts.insert name ci
  discard <| env.toKernelEnv.replay consts
  env.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  for arg in args do
    let module := arg.toName
    try
      replayModule module
    catch e =>
      IO.eprintln s!"kernel-check: {module}: {e}"
      return 1
    IO.println s!"ok {module}"
    (← IO.getStdout).flush
  return 0
