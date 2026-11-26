import Lean

/-!
# Axiom footprint of imported declarations

Run `lake env bash ../tools/axiom-footprint.sh PROJECT "MODULE [MODULE...]" DECLARATION...`
from a built project. The launcher clears the project search path while Lean loads this checker.
The checker takes the allowed declarations from the toolchain's `Init`. It then reads the
project's compiled modules and follows the dependencies of each named declaration.

The result is a footprint check on compiled objects. The build and kernel replay have their
own checks.
-/

open Lean

private def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

private def standardAxioms : IO (List (Name × AxiomVal)) := do
  let env ← importModules #[{ module := `Init }] {}
  allowed.mapM fun name => do
    let some (.axiomInfo info) := env.find? name
      | throw (IO.userError s!"missing standard axiom '{name}'")
    return (name, info)

private instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

def main (args : List String) : IO UInt32 := do
  let projectPath :: project :: modules :: declaration :: rest := args
    | IO.eprintln "usage: axiom-footprint.sh PROJECT \"MODULE [MODULE...]\" DECLARATION..."
      return 2
  let roots := modules.splitOn " "
  if roots.any String.isEmpty then
    IO.eprintln s!"error: {project}: expected one or more module names"
    return 2
  let builtinPath ← getBuiltinSearchPath (← findSysroot)
  searchPathRef.set builtinPath
  let expected ← standardAxioms
  searchPathRef.set (System.SearchPath.parse projectPath ++ builtinPath)
  let imports := roots.toArray.map fun name => ({ module := name.toName } : Import)
  let env ← importModules imports {} (loadExts := false)
  let mut passed := true
  for text in declaration :: rest do
    let name := text.toName
    if (env.find? name).isNone then
      IO.eprintln s!"error: {project}: unknown declaration '{name}'"
      passed := false
      continue
    let (axioms, _) := (collectAxioms (m := StateM Environment) name).run env
    if axioms.isEmpty then
      IO.println s!"'{name}' does not depend on any axioms"
    else
      IO.println s!"'{name}' depends on axioms: {axioms.toList}"
    for dependency in axioms do
      match expected.lookup dependency, env.find? dependency with
      | some standard, some (.axiomInfo found) =>
        unless found.type == standard.type && found.levelParams == standard.levelParams &&
            found.isUnsafe == standard.isUnsafe do
          IO.eprintln s!"error: {project}: {name} uses a changed standard axiom '{dependency}'"
          passed := false
      | _, _ =>
        IO.eprintln s!"error: {project}: {name} depends on more axioms: '{dependency}'"
        passed := false
  return if passed then 0 else 1
