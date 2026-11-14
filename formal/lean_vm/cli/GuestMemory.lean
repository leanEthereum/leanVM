import LeanVM.Guest.Data.Source
import LeanVM.Guest.Expand
import LeanVM.Guest.Renumber
import LeanVM.Guest.Memory.Fresh
import LeanVM.Guest.Memory.SizeTotal
import Std.Data.HashMap

/-!
# `guest-memory`: the guest's kernel-checked memory-layer facts

`lake exe guest-memory` writes the kernel checks of `Memory.memF` (`Memory/MemCheck.lean`) on the
guest's core IR (`coreProgram`, computed here as `guest-core` computes it:
`Expand.expandProgram Data.guest`, renumbered), under `LeanVM/Guest/Memory/GuestMem*`:

* `GuestMem/Data.lean`: `Data.takesT`, the arity of every function a `callIf` names, by index,
  and `temps{j}`, the temporaries of each function too large for one check;
* `GuestMem/Part*.lean`: `memRange_{a} : RangeOk (memF Data.takesT) a n`, ranges of functions;
* `GuestMem/Big{j}_*.lean`, `GuestMem/Fn{j}.lean`: a function too large for one check, by ranges
  of its statements (`mem{j}_{a}`), joined into `memRange_{j}`; `tmps{j}` its temporaries, all of
  them listed in `Data.bigTemps` (`bigTemps_spec`), which is what other modules read;
* `GuestMem.lean`: `memAll`, the ranges joined over the whole core IR, from which
  `Memory/GuestFresh.lean`, `GuestWf.lean` and `GuestMainFree.lean` derive their facts.

The ranges are cut by an estimate of their kernel cost (`cost`) and spread over modules of a few
checks each, which build in parallel. `--check` writes nothing and fails when a file differs;
`--stats` prints the costs. Run it from `lean_vm`.
-/

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

namespace GuestMemory

def memDir : System.FilePath := "LeanVM/Guest/Memory"

/-! ## Costs -/

mutual
def callIfs : Stmt → Nat
  | .ite _ z n => callIfsList z + callIfsList n
  | .match_ _ arms => callIfsArms arms
  | .callIf .. => 1
  | _ => 0
def callIfsList : List Stmt → Nat
  | [] => 0
  | s :: ss => callIfs s + callIfsList ss
def callIfsArms : List (List Stmt) → Nat
  | [] => 0
  | a :: as => callIfsList a + callIfsArms as
end

mutual
def stmtCount : Stmt → Nat
  | .ite _ z n => 1 + stmtCountList z + stmtCountList n
  | .match_ _ arms => 1 + stmtCountArms arms
  | _ => 1
def stmtCountList : List Stmt → Nat
  | [] => 0
  | s :: ss => stmtCount s + stmtCountList ss
def stmtCountArms : List (List Stmt) → Nat
  | [] => 0
  | a :: as => stmtCountList a + stmtCountArms as
end

mutual
def callIfTargets : Stmt → List String
  | .ite _ z n => callIfTargetsList z ++ callIfTargetsList n
  | .match_ _ arms => callIfTargetsArms arms
  | .callIf _ f _ => [f]
  | _ => []
def callIfTargetsList : List Stmt → List String
  | [] => []
  | s :: ss => callIfTargets s ++ callIfTargetsList ss
def callIfTargetsArms : List (List Stmt) → List String
  | [] => []
  | a :: as => callIfTargetsList a ++ callIfTargetsArms as
end

/-- The kernel cost of `memB` on statements: their values and statements walked, a callee lookup
(`calleeIdx`, comparing names) per `callIf`, and a name comparison per callee. -/
def cost (ss : List Stmt) : Nat :=
  (Stmt.usesList ss).length + stmtCountList ss + 100 * callIfsList ss + 5 * (Stmt.blockCallees ss).length

/-- One declaration's cost at most this (`cost` units). -/
def budget : Nat := 100000

/-- A range holds at most this many functions. -/
def maxFns : Nat := 150

/-- A module holds at most this many declarations, so that its kernel checks stay short. -/
def declsPerModule : Nat := 6

/-! ## Ranges -/

/-- Cut `lo .. hi` into ranges of cost at most `budget`, a range of one item if it alone exceeds
it: `(start, length, cost)`. -/
def cut (costs : Array Nat) (lo hi : Nat) : List (Nat × Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat × Nat) := #[]
  let mut a := lo
  let mut fuel := hi - lo + 1
  while a < hi && fuel > 0 do
    fuel := fuel - 1
    let mut n := 1
    let mut w := costs[a]!
    while a + n < hi && n < maxFns && w + costs[a + n]! ≤ budget do
      w := w + costs[a + n]!
      n := n + 1
    out := out.push (a, n, w)
    a := a + n
  return out.toList

/-- Group declarations into modules, at most four declarations' budget of cost and
`declsPerModule` each. -/
def modules {α : Type} (items : List (α × Nat)) : List (List α) := Id.run do
  let mut out : Array (List α) := #[]
  let mut cur : Array α := #[]
  let mut w := 0
  for (x, c) in items do
    if !cur.isEmpty && (w + c > 4 * budget || cur.size ≥ declsPerModule) then
      out := out.push cur.toList
      cur := #[]
      w := 0
    cur := cur.push x
    w := w + c
  if !cur.isEmpty then out := out.push cur.toList
  return out.toList

def lst (l : List Nat) : String := s!"[{", ".intercalate (l.map toString)}]"

/-- A long list literal as `::` (elaborated without nested `have`s). -/
def natList (l : List Nat) : String :=
  if l.length < 32 then lst l else s!"({" :: ".intercalate (l.map toString)} :: [])"

def pad2 (k : Nat) : String := if k < 10 then s!"0{k}" else toString k

/-- `Data.bigTemps`: the large functions `js` and their temporaries. -/
def bigList (js : List Nat) : String := s!"[{", ".intercalate (js.map fun j => s!"({j}, temps{j})")}]"

/-- `bigTemps_spec`'s last step, after `simp`: nothing, one function's `tmps`, or their tuple. -/
def bigProof (js : List Nat) : String :=
  match js with
  | [] => ""
  | [j] => s!"\n  exact tmps{j}"
  | _ => s!"\n  exact ⟨{", ".intercalate (js.map fun j => s!"tmps{j}")}⟩"

/-- A balanced `NTree ℕ` of the sorted items, a node per line. -/
partial def ntree (items : Array (Nat × Nat)) (lo hi : Nat) : String :=
  if lo ≥ hi then ".leaf" else
    let m := (lo + hi) / 2
    let (k, v) := items[m]!
    s!"(.node {k} {v}\n    {ntree items lo m}\n    {ntree items (m + 1) hi})"

/-! ## Files -/

def header (name doc : String) : String :=
  s!"/-\n  {name}\n\n  Generated by `lake exe guest-memory` (lean_vm/cli/GuestMemory.lean); do not edit.\n  {doc}\n-/\n\nmodule\n\n"

def nsOpen : String := "namespace LeanVM.Guest\n\nopen Core Memory\n\n@[expose] public section\n"

def nsClose : String := "\nend\nend LeanVM.Guest\n"

def chk : String := "(memF Data.takesT)"

def files (P : Program) : Array (System.FilePath × String) := Id.run do
  let costs := (P.map fun fn => cost fn.body).toArray
  let big := (List.range P.length).filter fun j => costs[j]! > budget
  -- the small functions' ranges, between the big ones
  let bounds := (0 :: big.map (· + 1)).zip (big ++ [P.length])
  let small := bounds.flatMap fun (lo, hi) => cut costs lo hi
  let gm := memDir / "GuestMem"
  let mut out : Array (System.FilePath × String) := #[]
  -- the data: arities and the big functions' temporaries
  let idx : Std.HashMap String Nat := P.zipIdx.foldl (fun m (fn, j) => m.insert fn.name j) {}
  let targets := (P.flatMap fun fn => callIfTargetsList fn.body).filterMap idx.get?
  let arities := ((targets.mergeSort (· ≤ ·)).eraseDups.map fun k => (k, P[k]!.params.length)).toArray
  let temps := String.join (big.map fun j =>
    s!"\nset_option maxRecDepth 100000 in\n/-- The temporaries of `{P[j]!.name}`'s range checks, in order. -/\ndef temps{j} : List ℕ := {natList ((Stmt.tmpsList P[j]!.body).map V.idx)}\n")
  out := out.push (gm / "Data.lean", header "LeanVM.Guest.Memory.GuestMem.Data"
    "The arities of the functions `callIf` names, and the large functions' temporaries." ++
    "public import LeanVM.Guest.Memory.MemCheck\n\n" ++ nsOpen ++
    s!"\n/-- The arity of every function a `callIf` names, by index. -/\ndef Data.takesT : NTree ℕ :=\n  {ntree arities 0 arities.size}\n" ++
    temps ++ s!"\n/-- The large functions' temporaries, by core index (`bigTemps_spec`). -/\ndef Data.bigTemps : List (ℕ × List ℕ) := {bigList big}\n" ++ nsClose)
  -- small ranges
  let decls := small.map fun (a, n, w) =>
    (s!"\nset_option maxRecDepth 100000 in\ntheorem memRange_{a} : RangeOk {chk} {a} {n} := by\n  unfold RangeOk; decide +kernel\n", w)
  let mut imports : Array String := #[]
  for (m, k) in (modules decls).zipIdx do
    let nm := s!"Part{pad2 k}"
    imports := imports.push s!"public import LeanVM.Guest.Memory.GuestMem.{nm}\n"
    out := out.push (gm / s!"{nm}.lean",
      header s!"LeanVM.Guest.Memory.GuestMem.{nm}" "Kernel checks of `memF` on ranges of the guest's functions." ++
      "public import LeanVM.Guest.Memory.GuestMem.Data\n\n" ++ nsOpen ++ String.join m ++ nsClose)
  -- big functions, by ranges of statements
  for j in big do
    let fn := P[j]!
    let body := fn.body.toArray
    let rngs := cut (body.map fun s => cost [s]) 0 body.size
    let body' := s!"Data.core{j}.body"
    let rdecls := rngs.map fun (a, n, w) =>
      (s!"\nset_option maxRecDepth 100000 in\ntheorem mem{j}_{a} : memBody Data.takesT {j} temps{j} (({body'}.drop {a}).take {n}) = true := by\n  decide +kernel\n", w)
    let mut names : Array String := #[]
    for (m, k) in (modules rdecls).zipIdx do
      let nm := s!"Big{j}_{k}"
      names := names.push nm
      out := out.push (gm / s!"{nm}.lean",
        header s!"LeanVM.Guest.Memory.GuestMem.{nm}" s!"Kernel checks of `memF` on ranges of `{fn.name}`'s statements." ++
        "public import LeanVM.Guest.Memory.GuestMem.Data\n\n" ++ nsOpen ++ String.join m ++ nsClose)
    let mut steps : Array String :=
      #[s!"  have h{body.size} : memBody Data.takesT {j} temps{j} ({body'}.drop {body.size}) = true :=\n    memBody_end (by decide +kernel)"]
    let mut prev := body.size
    for (a, n, _) in rngs.reverse do
      steps := steps.push s!"  have h{a} : memBody Data.takesT {j} temps{j} ({body'}.drop {a}) = true :=\n    memBody_drop (n := {n}) mem{j}_{a} h{prev}"
      prev := a
    let imps := String.join (names.toList.map fun nm => s!"public import LeanVM.Guest.Memory.GuestMem.{nm}\n")
    imports := imports.push s!"public import LeanVM.Guest.Memory.GuestMem.Fn{j}\n"
    out := out.push (gm / s!"Fn{j}.lean",
      header s!"LeanVM.Guest.Memory.GuestMem.Fn{j}" s!"`{fn.name}` passes `memF`, by ranges of its statements." ++
      imps ++ "\n" ++ nsOpen ++
      s!"\nset_option maxRecDepth 100000 in\n/-- `{fn.name}`'s temporaries, by index. -/\ntheorem tmps{j} : (Stmt.tmpsList {body'}).map V.idx = temps{j} := by\n  rw [← tmpsR_eq]; decide +kernel\n" ++
      s!"\nset_option maxRecDepth 100000 in\ntheorem head{j} : memHead Data.takesT {j} Data.core{j} temps{j} = true := by\n  decide +kernel\n" ++
      s!"\nset_option maxRecDepth 100000 in\ntheorem memRange_{j} : RangeOk {chk} {j} 1 := by\n" ++
      "\n".intercalate steps.toList ++
      s!"\n  exact RangeOk.one (fn := Data.core{j}) rfl (memF_of ((tmpsR_eq _).trans tmps{j}) head{j} h0)\n" ++ nsClose)
  -- the whole program
  let pieces : List (Nat × Nat) := ((small.map fun ((a, n, _) : Nat × Nat × Nat) => (a, n)) ++ big.map (fun j => (j, 1))).mergeSort
    (fun x y => x.1 ≤ y.1)
  let mut steps : Array String := #[]
  let mut tot := 0
  for ((a, n), i) in pieces.zipIdx do
    tot := tot + n
    steps := steps.push (if i == 0 then s!"  have h0 : RangeOk {chk} 0 {tot} := memRange_{a}"
      else s!"  have h{i} : RangeOk {chk} 0 {tot} := h{i - 1}.append (m := {n}) memRange_{a}")
  out := out.push (memDir / "GuestMem.lean",
    header "LeanVM.Guest.Memory.GuestMem"
      "Every function of the guest's core IR passes the memory check (`memAll`)." ++
    String.join imports.toList ++ "
/-!
# The guest's memory check

`Memory.memF` is evaluated by the kernel on ranges of `coreProgram`'s functions (`memRange_*`,
`GuestMem/Part*.lean`); a function too large for one check by ranges of its statements
(`GuestMem/Fn*.lean`). The ranges concatenate to the whole program.
-/

" ++ nsOpen ++ s!"
set_option maxRecDepth 100000 in
/-- **Every function of the guest passes the memory check.** -/
theorem memAll : RangeOk {chk} 0 coreProgram.length := by
" ++ "\n".intercalate steps.toList ++ s!"
  rw [coreProgram_length]; exact h{pieces.length - 1}

set_option maxRecDepth 100000 in
/-- **The large functions' temporaries**: those `Data.bigTemps` lists. -/
theorem bigTemps_spec :
    ∀ p ∈ Data.bigTemps, (Stmt.tmpsList (coreProgram.getD p.1 default).body).map V.idx = p.2 := by
  rw [← List.forall_iff_forall_mem]
  simp only [Data.bigTemps, List.Forall]{bigProof big}
" ++ nsClose)
  return out

end GuestMemory

open GuestMemory

/-- Every Lean file of a directory. -/
def listLean (d : System.FilePath) : IO (List System.FilePath) := do
  if !(← d.pathExists) then return []
  let es ← d.readDir
  return (es.filter (·.path.extension == some "lean")).toList.map (·.path)

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let program ← match Expand.expandProgram Data.guest with
    | .ok fns => pure (fns.map Fn.renumber)
    | .error e => throw (IO.userError s!"expansion: {e}")
  if args.contains "--stats" then
    for (fn, j) in program.zipIdx do
      IO.println s!"{j} {fn.name} cost {cost fn.body} stmts {fn.body.length}"
    return 0
  let fs := files program
  let dir := memDir / "GuestMem"
  let mut bad := false
  if check then
    for (p, s) in fs do
      -- Two steps: a `(← …)` is run before the `||`, so a missing file must not be read.
      let same ← if ← p.pathExists then pure ((← IO.FS.readFile p) == s) else pure false
      if !same then
        IO.eprintln s!"stale: {p}"
        bad := true
    for p in ← listLean dir do
      if !fs.any (·.1 == p) then
        IO.eprintln s!"stale: {p}"
        bad := true
  else
    for p in ← listLean dir do
      if !fs.any (·.1 == p) then IO.FS.removeFile p
    IO.FS.createDirAll dir
    for (p, s) in fs do
      IO.FS.writeFile p s
    IO.println s!"wrote {fs.size} files"
  return if bad then 1 else 0
