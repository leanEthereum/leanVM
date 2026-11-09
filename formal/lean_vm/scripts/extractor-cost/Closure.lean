/-
  The dependency closure of the knowledge extractor, as a compiler to a cost machine would have to
  handle it: every definition `transcriptExtractor` reaches through definition bodies (not proofs,
  not types), with the constructs that matter to such a compiler flagged. Spike evidence.
  `cd lean_vm && lake env lean --run scripts/extractor-cost/Closure.lean`
-/
import Lean
import LeanVM.Protocol.Extraction.Extractor

open Lean

/-- The constants a definition's body uses, outside proofs and types it does not compute. -/
def bodyConsts (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.defnInfo d) => d.value.getUsedConstants
  | some (.opaqueInfo d) => d.value.getUsedConstants
  | _ => #[]

def isProofLike (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.thmInfo _) => true
  | some (.axiomInfo _) => true
  | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => true
  | _ => false

def flags (env : Environment) (c : Name) : List String := Id.run do
  let us := bodyConsts env c
  let has (p : Name → Bool) := us.any p
  let mut fs : List String := []
  if has (fun n ↦ n == ``WellFounded.fix || n.toString.endsWith "_unary") then fs := "wf" :: fs
  if has (fun n ↦ (`Std.HashMap).isPrefixOf n || (`Std.DHashMap).isPrefixOf n) then
    fs := "hashmap" :: fs
  if has (fun n ↦ n == ``Array.set || n == ``Array.set! || n == ``Array.setIfInBounds ||
      n == ``Array.modify) then fs := "array-set" :: fs
  if has (fun n ↦ n == ``Nat.mul || n == ``Nat.pow || n == ``Nat.div || n == ``Nat.choose) then
    fs := "nat-arith" :: fs
  if has (fun n ↦ (`Vector).isPrefixOf n) then fs := "vector" :: fs
  if has (fun n ↦ (`Fin).isPrefixOf n) then fs := "fin" :: fs
  if has (fun n ↦ (`Float).isPrefixOf n || (`Real).isPrefixOf n) then fs := "real/float" :: fs
  if (Compiler.getImplementedBy? env c).isSome then fs := "implementedBy" :: fs
  if isExtern env c then fs := "extern" :: fs
  -- (the instance extension's state is not loaded without initializers: instances by name)
  if c.components.any (fun n ↦ n.toString.startsWith "inst") then fs := "instance" :: fs
  return fs

def modOf (env : Environment) (c : Name) : String :=
  match env.getModuleIdxFor? c with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => "?"

def topOf (m : String) : String :=
  match m.splitOn "." with
  | a :: _ => a
  | [] => m

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanVM.Protocol.Extraction.Extractor }] {} 0 (loadExts := false)
  let root : Name := match args with
    | r :: _ => r.toName
    | [] => `LeanVM.transcriptExtractor
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if isProofLike env c then continue
    for d in bodyConsts env c do
      if !seen.contains d then todo := todo.push d
  let defs := seen.toArray.filter fun c ↦
    match env.find? c with
    | some (.defnInfo _) | some (.opaqueInfo _) => true
    | _ => false
  -- per top-level package, the definitions and their flags
  let mut byTop : Std.HashMap String (Nat × Std.HashMap String Nat) := {}
  for c in defs do
    let t := topOf (modOf env c)
    let (n, fm) := byTop.getD t (0, {})
    let mut fm := fm
    for f in flags env c do fm := fm.insert f (fm.getD f 0 + 1)
    byTop := byTop.insert t (n + 1, fm)
  -- source lines of the definitions, per package (their declaration ranges)
  let mut lines : Std.HashMap String Nat := {}
  for c in defs do
    let t := topOf (modOf env c)
    if let some r := declRangeExt.find? (level := .server) env c then
      lines := lines.insert t (lines.getD t 0 + (r.range.endPos.line - r.range.pos.line + 1))
  IO.println s!"closure of {root}: {defs.size} definitions"
  for (t, (n, fm)) in byTop.toArray.qsort (fun a b ↦ a.1 < b.1) do
    IO.println s!"  {t}: {n} definitions, {lines.getD t 0} source lines; {fm.toList}"
  -- the definitions with the hard flags, outside the core library
  for c in defs.qsort Name.lt do
    let fs := flags env c
    let t := topOf (modOf env c)
    if (t == "Statement" || t == "CompPoly") &&
        fs.any (fun f ↦ f == "wf" || f == "hashmap" || f == "real/float" ||
          f == "implementedBy") then
      IO.println s!"    {c} [{modOf env c}] {fs}"
