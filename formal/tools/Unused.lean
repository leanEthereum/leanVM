import Lean

/-!
# Declarations nothing uses

`lake env lean --run ../tools/Unused.lean ROOT... [--prefix P]...`, from a project's directory after
building it: the repository's theorems and definitions, in the modules whose names start with a
prefix `P` (default: the roots' first components), that no declaration of any module the roots
import mentions, in its statement, its value or its proof. Give as roots the project's end module
and its tests, so that what they check counts as used.

A declaration nothing uses is either a result of the project (an end theorem, which the end module
mentions, or a lemma kept for a reader) or dead: proved, compiled and maintained for nothing. The
list is a starting point for deleting, read before deleting: instances, `@[simp]` and `@[csimp]`
lemmas and attributes act without being named, and are reported apart. The executables (`lean_vm/cli/`) cannot be roots
together (each declares `main`): what only they use is reported unused, so build them after
deleting.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let rec split : List String → List String × List String
    | "--prefix" :: p :: rest => let (r, ps) := split rest; (r, p :: ps)
    | "--spans" :: rest => split rest
    | a :: rest => let (r, ps) := split rest; (a :: r, ps)
    | [] => ([], [])
  let (roots, prefixes) := split args
  if roots.isEmpty then
    IO.eprintln "usage: lake env lean --run Unused.lean ROOT... [--prefix P]..."; return 2
  let prefixes : List Name := if prefixes.isEmpty then roots.map fun r ↦ r.toName.getRoot
    else prefixes.map String.toName
  initSearchPath (← findSysroot)
  -- every module the roots import, its private part included, so that proofs are seen
  let env0 ← importModules (roots.toArray.map fun r ↦ ({ module := r.toName } : Import)) {}
    (loadExts := false)
  let ours := env0.header.moduleNames.filter fun m ↦ prefixes.any (·.isPrefixOf m)
  let env ← importModules (ours.map (fun m ↦ ({ module := m, importAll := true } : Import)) ++
    roots.toArray.map fun r ↦ ({ module := r.toName } : Import)) {} (loadExts := false)
  let modOf (c : Name) : Option Name := (env.getModuleIdxFor? c).map (env.header.moduleNames[·.toNat]!)
  let isOurs (c : Name) : Bool := (modOf c).any fun m ↦ prefixes.any (·.isPrefixOf m)
  -- references from every declaration of the environment
  let mut used : NameSet := {}
  for (_, ci) in env.constants.map₁.toList do
    for u in ci.type.getUsedConstants do used := used.insert u
    if let some v := ci.value? (allowOpaque := true) then
      for u in v.getUsedConstants do used := used.insert u
  -- a structure's projections and constructors, a definition's equations: used with it
  let mut unused : Array (Name × Name × String) := #[]
  for (c, ci) in env.constants.map₁.toList do
    if !isOurs c || used.contains c || c.isInternalDetail || isPrivateName c then continue
    -- what Lean generates: projections, recursors, matchers, equation and congruence lemmas
    if env.isProjectionFn c || isAuxRecursor env c || isNoConfusion env c || isRecCore env c ||
        Meta.isMatcherCore env c || isCasesOnRecursor env c then continue
    if c.isStr && ["congr_simp", "injEq", "inj", "sizeOf_spec", "eq_def", "ext_iff", "ctorIdx",
        "induct", "mutual_induct", "fun_cases", "elim"].contains c.getString! then continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
      | _ => ""
    if kind.isEmpty then continue
    let last := c.getString!
    if last.startsWith "eq_" || last == "eq_def" || last.startsWith "match_" ||
        last.startsWith "proof_" then continue
    let acts := (Meta.isInstanceCore env c) || (Meta.simpExtension.getState env).lemmaNames.contains (.decl c)
    let (lines, span) := match declRangeExt.find? env c with
      | some r => (r.range.endPos.line - r.range.pos.line + 1,
          s!" {r.range.pos.line}-{r.range.endPos.line}")
      | none => (0, "")
    unused := unused.push ((modOf c).getD .anonymous, c,
      s!"{kind}{if acts then " (acts unnamed)" else ""} {lines} lines{if args.contains "--spans" then span else ""}")
  let sorted := unused.qsort fun a b ↦ a.1.toString < b.1.toString ||
    (a.1 == b.1 && a.2.1.toString < b.2.1.toString)
  for (m, c, k) in sorted do
    IO.println s!"{m} {c} {k}"
  IO.eprintln s!"{sorted.size} declarations nothing uses, in {ours.size} modules"
  return 0
