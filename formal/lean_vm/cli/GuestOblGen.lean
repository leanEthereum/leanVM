import LeanVMTests.Guest.CoreDataCheck

/-!
# `guest-oblgen`: the guest's data of the soundness obligations

The back end's obligations at the guest (`Guest/Compiled/Obl/`) are proved by hand over a few tables of
guest functions and by kernel evaluation over runs of them. This writes, from the guest's core
program (`Data.coreFunctions`, read from the `.olean`s of `LeanVM.Guest.CoreData`) and its
functions' stable names (`Data/Names.lean`), what of that depends on the guest's numbering:

* `Obl/GuestXTab.lean`: the `ext` families, `mainTab` (the `opening_queries` specializations, their
  shapes from B1's `openingQueriesShapes` and the loop helper each body calls), `loopTab` (those
  loop helpers), `lqTab` (the `level_queries` specializations and the specialization each calls),
  `osTab` (`open_stacked__L{m}` and their pairs of sites: each top-level dispatch into
  `level_queries` with the last dispatch into `level_positions` before it);
* in `Obl/GuestX.lean` the list `xTab`, and in `Obl/GuestTab.lean` the lists `guestXIdx` (the
  families' indices with `verify_bus_gkr` and `verify_bus_gkr_loop0`) and `vsIdx` (`verify_sub`):
  each declaration replaced whole, up to the blank line after it, the rest of the file untouched;
* `Obl/Eval/E{kk}.lean`: the analysis over runs of functions, the runs starting at the functions
  `anchors` names by stable name;
* `Obl/Eval/XMain.lean`, `XLoop0/1`, `XLq`, `XOs0/1`: the families' checks over runs of entries;
* `Obl/Eval/Misc.lean`: `verify_sub`'s analysis with its facts and the count of functions;
* `Obl/Eval/All.lean`: the runs assembled (`guest_chk_all`, `mainTab_ok`, `loopTab_ok`,
  `lqTab_ok`, `osTab_ok`).

The hand-written facts are about functions the generator is told the stable names of (`handFacts`,
`postNames`, every key of `guestTab`, read from `GuestTab.lean`): a name the guest no longer has
fails here, naming the fact, as does a function of `tabFamilies` with no entry in `guestTab`.
A run's anchor the guest no longer has merges its run into the one before, and is reported.

`lake exe guest-oblgen --check` writes nothing and fails when a file differs, or when `Eval/` holds
a file not written here. Run under `lake env` (as `lake exe` does) after the core data and
`B1.Opening.Interface` are built (`scripts/regen-guest.sh`, step `backend`).
-/

open Lean LeanVM.Guest LeanVM.Guest.Core
open LeanVMTests.Guest.CoreData (R list fn nat str app bad unfold)

namespace GuestOblGen

def oblDir : System.FilePath := "LeanVM/Guest/Compiled/Obl"
def evalDir : System.FilePath := oblDir / "Eval"

/-- The hand-written facts' functions, by stable name, with what each fact is. -/
def handFacts : List (String × String) := [
  ("verify_sub", "`vsIdx`, `vsFacts` (GuestTab), `evalVs`, `vs_fn`, `vs_xpre` (Eval/Misc), GuestB1"),
  ("verify_bus_gkr", "`gkrBus_obl` (Gkr), `guestXIdx`"),
  ("verify_bus_gkr_loop0", "`gkrLoop_obl` (Gkr), `xTab`'s `.gkr`, `guestXIdx`"),
  ("exponent_tables", "`guestTab_xpost` (Eval/Misc), `ExpPost` (Guest)"),
  ("main_loop2", "`guestTab.pows`, its range checks' bound"),
  ("list_split", "`postNames` (Eval/Misc)"),
  ("log2_ceil_in_the_exponent__L0_L34", "`postNames` (Eval/Misc)")]

/-- The functions with a postcondition in `guestTab` (`Eval/Misc.postNames`), by stable name. -/
def postNames : List String := ["list_split", "log2_ceil_in_the_exponent__L0_L34"]

/-- The families of which every function has an entry in `guestTab` (by its name). -/
def tabFamilies : List String := ["level_positions__L", "walk_path__L", "open_stacked__L"]

/-- The runs of `Eval/E{kk}`, module by module, by the stable name of each run's first function:
the costly functions alone (`verify_tables`, `main_loop2`), the others in runs of a few seconds. -/
def anchors : List (List String) := [
  ["main", "verify_tables", "verify_keccak", "main_loop2", "main_loop3", "eq_prefix_run__L23",
    "rs_eq_rows__L6"],
  ["padding_weight__L16", "plus_one_run__L10", "block_selector__L1", "block_selector__L26",
    "index_mle__L17", "block_selector_tab__L8", "block_selector_tab__L33"],
  ["column_selector__L14", "squeeze_point_from__L25", "claim_list_last__L1",
    "child_claim_list_last__L7", "child_claim_list_mono_last__L13", "da_column_offsets_loop1",
    "grind_check__L19"],
  ["level_positions__L4_L13_L7", "level_positions__L10_L19_L7", "level_positions__L16_L18_L6",
    "squeeze_point_from__L17", "level_residual__L25_L9_L4_L2", "level_residual__L19_L6_L4_L2",
    "level_residual__L19_L7_L4_L2"],
  ["level_residual__L18_L8_L4_L2", "level_positions__L22_L24_L6", "level_residual__L16_L6_L4_L2",
    "level_residual__L18_L11_L4_L2", "level_residual__L21_L12_L4_L2"],
  ["level_positions__L5_L16_L4_loop0", "level_residual__L44_L10_L4_L2_loop1",
    "level_residual__L109_L15_L6_L3_loop0", "opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0",
    "level_residual__L25_L8_L4_L2_loop1", "level_residual__L44_L13_L4_L2_loop1",
    "level_residual__L109_L18_L6_L3_loop1"],
  ["level_positions__L37_L20_L8_loop0", "level_residual__L37_L15_L4_L2_loop1",
    "opening_queries__L0_L0_L4_L16_L18_L6_L4_L10_L20_L5_L1", "level_residual__L18_L8_L4_L2_loop0",
    "level_residual__L37_L17_L4_L2_loop1", "level_positions__L3_L22_L4_loop0",
    "level_residual__L19_L10_L4_L2_loop1"],
  ["level_residual__L55_L23_L6_L3_loop0", "level_positions__L28_L26_L2_loop0",
    "level_residual__L32_L20_L4_L2_loop0",
    "opening_queries__L1_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0_loop0"]]

/-- `XMain`'s entries per run, `XLoop0/1`'s, `XLq`'s runs, `XOs0/1`'s entries per run. -/
def mainRun : Nat := 10
def loopRun : Nat := 8
def lqRuns : Nat := 4
def osRun : Nat := 1

/-! ## Reading the guest -/

/-- B1's `OqShape`: its eleven numbers and `vs`. -/
structure Shape where
  ps : List Nat
  vs : List Nat
  deriving BEq

/-- `e` with its outer `let`s and `have`s substituted (a long list literal elaborates to them). -/
partial def zeta : Expr → Expr
  | .letE _ _ v b _ => zeta (b.instantiate1 v)
  | .mdata _ e => zeta e
  | e => e

/-- A list literal, through the `let`s of its elaboration. -/
partial def zlist {α : Type} (f : Expr → R α) (e : Expr) : R (List α) := do
  let e := zeta (← unfold (zeta e))
  match e.getAppFnArgs with
  | (``List.nil, #[_]) => return []
  | (``List.cons, #[_, h, t]) => return (← f (zeta h)) :: (← zlist f t)
  | _ => bad "a list" e

def shape (e : Expr) : R Shape := do
  match ← app e with
  | (`LeanVM.Guest.B1.OqShape.mk, args) =>
      if args.size != 12 then bad "an OqShape" e
      else return ⟨← (args.extract 0 11).toList.mapM (nat ∘ zeta), ← zlist nat args[11]!⟩
  | _ => bad "an OqShape" e

def namedShape (e : Expr) : R (String × Shape) := do
  match ← app e with
  | (``Prod.mk, #[_, _, a, b]) => return (← str (zeta a), ← shape (zeta b))
  | _ => bad "a pair" e

/-- The guest as the generator reads it. -/
structure Guest where
  fns : Array Fn
  /-- Each function's stable name, by index. -/
  stable : Array String
  /-- B1's shapes of the `opening_queries` specializations, by name. -/
  shapes : List (String × Shape)

def defValue (env : Environment) (n : Name) : Except String Expr :=
  match env.find? n with
  | some (.defnInfo d) => .ok d.value
  | _ => .error s!"no definition {n}"

/-- The guest, from the environment of `CoreData` and `B1.Opening.Interface`. -/
def readGuest (env : Environment) : Except String Guest := do
  let fns ← (list fn (← defValue env `LeanVM.Guest.Data.coreFunctions)).run env
  let count ← (nat (← defValue env `LeanVM.Guest.Data.coreCount)).run env
  unless fns.length == count do throw s!"coreCount {count}, but {fns.length} core functions"
  let some mi := env.getModuleIdx? `LeanVM.Guest.Data.Names | throw "no module Data.Names"
  let some md := env.header.moduleData[mi.toNat]? | throw "no data of Data.Names"
  let iNs := `LeanVM.Guest.Data.I
  let mut slots : Array (Option String) := Array.replicate count none
  for n in md.constNames do
    if n.getPrefix == iNs then
      if let .str _ s := n then
        let j ← (nat (← defValue env n)).run env
        unless j < count && slots[j]!.isNone do throw s!"Data.I.«{s}» := {j}: not a free index"
        slots := slots.set! j (some s)
        let nm ← (str (← defValue env (`LeanVM.Guest.Data.N ++ .str .anonymous s))).run env
        unless nm == fns[j]!.name do throw s!"Data.N.«{s}» is {nm}, function {j} is {fns[j]!.name}"
  let stable ← slots.mapIdxM fun j s? => match s? with
    | some s => pure s
    | none => throw s!"function {j} has no stable name"
  let shapes ← (zlist namedShape (← defValue env `LeanVM.Guest.B1.openingQueriesShapes)).run env
  return ⟨fns.toArray, stable, shapes⟩

/-! ## The families -/

/-- The functions a block calls, every branch and arm. -/
partial def calls : List Stmt → List String
  | [] => []
  | s :: ss =>
    let here := match s with
      | .call f _ _ => [f]
      | .callIf _ f _ => [f]
      | .dispatch _ fs _ _ => fs
      | .ite _ z e => calls z ++ calls e
      | .match_ _ arms => arms.flatMap calls
      | .atom _ | .ret _ => []
    here ++ calls ss

/-- The numbers of a specialization's name `{pre}__L{a}_L{b}…`. -/
def nums (pre name : String) : Option (List Nat) :=
  if name.startsWith (pre ++ "__L") then
    ((name.drop (pre.length + 3)).toString.splitOn "_L").mapM String.toNat?
  else none

/-- The walk's shape of a specialization's shape: depth, cap depth, `odd`, `base`. -/
def walkOf (s : Shape) : String :=
  s!"⟨{s.ps.getD 4 0}, {s.ps.getD 5 0}, {s.ps.getD 0 0}, {s.ps.getD 1 0}⟩"

def pShape (s : Shape) : String :=
  s!"⟨{", ".intercalate (s.ps.map toString)}, [{", ".intercalate (s.vs.map toString)}]⟩"

structure Main where
  idx : Nat
  name : String
  shape : Shape
  loop : String
  loopIdx : Nat

structure Lq where
  idx : Nat
  name : String
  main : String
  n : Nat
  walk : String

structure Tables where
  mains : List Main
  loops : List Main
  lqs : List Lq
  os : List (Nat × String × List (Nat × Nat))
  gkrBus : Nat
  gkrLoop : Nat
  gkrLoopName : String
  vs : Nat
  xIdx : List Nat

def sortBy {α : Type} (f : α → Nat) (l : List α) : List α := l.mergeSort fun a b => f a ≤ f b

def tables (G : Guest) : Except String Tables := do
  let idxOf : Std.HashMap String Nat := G.fns.foldl (init := {}) fun m f => m.insert f.name m.size
  let stableIdx : Std.HashMap String Nat :=
    (List.range G.stable.size).foldl (init := {}) fun m j => m.insert G.stable[j]! j
  let byStable (s : String) : Except String Nat := match stableIdx[s]? with
    | some j => .ok j
    | none => .error s!"no core function of stable name {s}"
  let named (pre : String) : List (Nat × Fn) :=
    (List.range G.fns.size).filterMap fun j =>
      if G.fns[j]!.name.startsWith (pre ++ "__L") then some (j, G.fns[j]!) else none
  let shapeOf (name : String) : Except String Shape := do
    let some s := G.shapes.lookup name | throw s!"{name} has no shape in openingQueriesShapes"
    unless nums "opening_queries" name == some s.ps do throw s!"{name}'s shape {pShape s}"
    return s
  let mains ← (named "opening_queries").mapM fun (j, f) => do
    let s ← shapeOf f.name
    match (calls f.body).filter (·.startsWith "__loop") |>.eraseDups with
    | [l] =>
      let some li := idxOf[l]? | throw s!"{f.name} calls {l}, not a core function"
      return { idx := j, name := f.name, shape := s, loop := l, loopIdx := li : Main }
    | ls => throw s!"{f.name} calls the loop helpers {ls}, not one"
  let loops := sortBy (·.loopIdx) mains
  unless (loops.map (·.loopIdx)).eraseDups.length == loops.length do
    throw "two opening_queries specializations share a loop helper"
  let lqs ← (named "level_queries").mapM fun (j, f) => do
    match (calls f.body).filter (·.startsWith "opening_queries__L") |>.eraseDups with
    | [m] =>
      let s ← shapeOf m
      let some q := (nums "level_queries" f.name).bind (·.head?) | throw s!"{f.name}: no count"
      let (odd, base) := (s.ps.getD 0 0, s.ps.getD 1 0)
      unless base != 1 || (q - odd) % 2 == 0 && odd ≤ q do throw s!"{f.name}: odd count at level 0"
      let n := if base == 1 then (q - odd) / 2 else q
      return { idx := j, name := f.name, main := m, n := n, walk := walkOf s : Lq }
    | ms => throw s!"{f.name} calls the specializations {ms}, not one"
  let os ← (named "open_stacked").mapM fun (j, f) => do
    let callsInto (pre : String) : Stmt → Bool
      | .dispatch _ fs _ _ => !fs.isEmpty && fs.all (·.startsWith pre)
      | _ => false
    let body := f.body.toArray
    let sites := (List.range body.size).filterMap fun i =>
      if callsInto "level_queries__L" body[i]! then
        ((List.range i).reverse.find? fun k => callsInto "level_positions__L" body[k]!).map (i, ·)
      else none
    let nq := (List.range body.size).countP fun i => callsInto "level_queries__L" body[i]!
    unless nq == sites.length && nq > 0 do throw s!"{f.name}: a level_queries dispatch with no level_positions dispatch before it"
    return (j, f.name, sites)
  let gkrBus ← byStable "verify_bus_gkr"
  let gkrLoop ← byStable "verify_bus_gkr_loop0"
  let vs ← byStable "verify_sub"
  if mains.isEmpty || lqs.isEmpty || os.isEmpty then throw "a family of ext functions is empty"
  let xIdx := (gkrBus :: gkrLoop :: os.map (·.1) ++ lqs.map (·.idx) ++ mains.map (·.idx) ++
    loops.map (·.loopIdx)).mergeSort
  unless xIdx.eraseDups.length == xIdx.length do throw "a function is in two ext families"
  return { mains, loops, lqs, os, gkrBus, gkrLoop, gkrLoopName := G.fns[gkrLoop]!.name, vs, xIdx }

/-! ## The text -/

def header (m what : String) : String :=
  s!"/-\n  LeanVM.Guest.Compiled.Obl.{m}\n\n  {what}\n-/\n\nmodule\n\n"

def opening : String :=
  "\nnamespace LeanVM.Guest.Compiled.Obl\n\nopen LeanVM.Compiler LeanVM.Compiler.Obl LeanVM.Guest\n\n@[expose] public section\n"

def closing : String := "\nend\nend LeanVM.Guest.Compiled.Obl\n"

/-- A list literal's items, four deep, the last closing it. -/
def items (xs : List String) : String :=
  String.join ((xs.zipIdx).map fun (x, i) =>
    s!"    {x}{if i + 1 == xs.length then "]" else ","}\n")

def guestXTab (T : Tables) : String :=
  header "GuestXTab" "The guest's functions the analysis checks with `ext` sites, by family, with their shapes." ++
  "public import LeanVM.Guest.B1.Opening.Interface

/-!
# The `ext` sites' functions

By index in `coreProgram` and name: the `opening_queries` specializations with their template's
shape (B1's `OqShape`, the name's numbers and the folding's `vs`) and loop helper, the loop helpers
with their shape and `odd`, the `level_queries` specializations with the specialization they call,
and `open_stacked__L0` to `__L10` with their pairs of sites (`level_queries`' dispatch,
`level_positions`' before it). The checks (`mainOk`, `loopOk`, `lqOk`, `osOk`) decide each entry.
-/

namespace LeanVM.Guest.Compiled.Obl

open LeanVM.Guest.B1

@[expose] public section

/-- The `opening_queries` specializations: index, name, shape, loop helper. -/
def mainTab : List (Nat × String × OqShape × String) := [
" ++ items (T.mains.map fun m => s!"({m.idx}, {m.name.quote}, {pShape m.shape}, {m.loop.quote})") ++ "
/-- The loop helpers: index, name, shape, `odd`. -/
def loopTab : List (Nat × String × OqShape × Nat) := [
" ++ items (T.loops.map fun m =>
    s!"({m.loopIdx}, {m.loop.quote}, {pShape m.shape}, {m.shape.ps.getD 0 0})") ++ "
/-- The `level_queries` specializations: index, name, the specialization it calls. -/
def lqTab : List (Nat × String × String) := [
" ++ items (T.lqs.map fun l => s!"({l.idx}, {l.name.quote}, {l.main.quote})") ++ "
/-- `open_stacked__L0` to `__L10`: index, the pairs of sites. -/
def osTab : List (Nat × List (Nat × Nat)) := [
" ++ items (T.os.map fun (j, _, ps) =>
    s!"({j}, [{", ".intercalate (ps.map fun (i, k) => s!"({i}, {k})")}])") ++ closing

/-- `xTab`, the declaration in `GuestX.lean`. -/
def xTabDecl (T : Tables) : String :=
  "def xTab : List (String × XSpec) := [\n" ++ items (
    s!"({T.gkrLoopName.quote}, .gkr)" ::
    T.mains.map (fun m => s!"({m.name.quote}, .main {walkOf m.shape})") ++
    T.loops.map (fun m => s!"({m.loop.quote}, .loop {walkOf m.shape})") ++
    T.lqs.map fun l => s!"({l.name.quote}, .lq {l.n} {l.walk})")

/-- Numbers as a list literal, broken at 100 columns. -/
def wrapNats (xs : List Nat) : String := Id.run do
  let toks := (xs.zipIdx).map fun (x, i) => s!"{x}{if i + 1 == xs.length then "]" else ","}"
  let mut lines : Array String := #[]
  let mut cur := "  ["
  for t in toks do
    if cur == "  [" then cur := cur ++ t
    else if cur.length + 1 + t.length > 100 then
      lines := lines.push cur
      cur := "  " ++ t
    else cur := cur ++ " " ++ t
  lines := lines.push cur
  return "\n".intercalate lines.toList ++ "\n"

/-- `guestXIdx` and `vsIdx`, the declarations in `GuestTab.lean`. -/
def guestXIdxDecl (T : Tables) : String := "def guestXIdx : List Nat :=\n" ++ wrapNats T.xIdx
def vsIdxDecl (T : Tables) : String := s!"def vsIdx : Nat := {T.vs}\n"

/-- A run: its first entry and its length. -/
abbrev Run := Nat × Nat

def eModule (k a b : Nat) (runs : List Run) : String :=
  let m := s!"E{if k < 10 then "0" else ""}{k}"
  header s!"Eval.{m}" s!"The analysis accepts the guest's functions {a} to {b}, by kernel evaluation." ++
  "public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Compiled.Obl.GuestTab
" ++ opening ++ String.join (runs.map fun (s, n) => s!"
/-- **The analysis accepts functions `{s}` to `{s + n - 1}`** of the guest's core program, but those it
skips (`guestSkip`). -/
theorem evalE_{s} : (List.range' {s} {n}).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  decide +kernel
") ++ closing

/-- A family's check over runs of its table. -/
structure Fam where
  tab : String
  thm : String
  check : String

def mainFam : Fam := ⟨"mainTab", "evalMain", "mainOk e.1 e.2.1 e.2.2.1 e.2.2.2"⟩
def loopFam : Fam := ⟨"loopTab", "evalLoop", "loopOk e.1 e.2.1 e.2.2.1 e.2.2.2"⟩
def lqFam : Fam := ⟨"lqTab", "evalLq", "lqOk e.1 e.2.1 e.2.2"⟩
def osFam : Fam := ⟨"osTab", "evalOs", "osOk e.1 e.2"⟩

def xModule (m what imp : String) (F : Fam) (runs : List Run) : String :=
  header s!"Eval.{m}" what ++ s!"public import LeanVM.Guest.Compiled.Obl.{imp}
public import LeanVM.Guest.Compiled.Obl.GuestXTab
" ++ opening ++ String.join (runs.map fun (s, n) => s!"
/-- **Entries `{s}` to `{s + n - 1}` of `{F.tab}` pass their check.** -/
theorem {F.thm}_{s} : (({F.tab}.drop {s}).take {n}).all (fun e => {F.check}) = true := by
  decide +kernel
") ++ closing

/-- `[a, b)` in runs of `r`. -/
def runsOf (a b r : Nat) : List Run :=
  (List.range ((b - a + r - 1) / r)).map fun i => (a + i * r, min r (b - a - i * r))

def misc (count : Nat) (vsParams : String) : String :=
  header "Eval.Misc" "The guest's facts the composition reads off the data: `verify_sub` with B1's facts, the
  table's postconditions and relations, the skipped functions' names." ++
  "public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Compiled.Obl.GuestTab
public import LeanVM.Compiler.Sound.Obl.CheckSound

namespace LeanVM.Guest.Compiled.Obl

open LeanVM.Compiler LeanVM.Compiler.Obl LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The analysis accepts `verify_sub`** with B1's facts (`vsFacts`). -/
theorem evalVs : chkFnF guestTab vsFacts (Data.coreFunctions.getD vsIdx default) = true := by
  decide +kernel

/-- `verify_sub`'s name and parameters. -/
theorem vs_fn : (Data.coreFunctions.getD vsIdx default).name = \"verify_sub\" ∧
    (Data.coreFunctions.getD vsIdx default).params = " ++ vsParams ++ " := by
  decide +kernel

/-- `verify_sub` takes the exponent table as argument `4`. -/
theorem vs_xpre : (guestTab.sig \"verify_sub\").xpre = [(4, 0)] := by decide +kernel

/-- The guest's core program has `" ++ toString count ++ "` functions. -/
theorem core_length : Data.coreFunctions.length = " ++ toString count ++ " := by decide +kernel

/-- Only `exponent_tables` has an `xpost`: its return is in relation `0`. -/
theorem guestTab_xpost : ∀ p ∈ guestTab.sigs, p.2.xpost ≠ [] →
    p.1 = \"exponent_tables\" ∧ p.2.xpost = [(0, 0)] := by
  decide +kernel

/-- The functions with a postcondition. -/
def postNames : List String := [" ++ ", ".intercalate (postNames.map String.quote) ++ "]

/-- Only `postNames` have a postcondition. -/
theorem guestTab_post : ∀ p ∈ guestTab.sigs, p.2.post ≠ [] → p.1 ∈ postNames := by
  decide +kernel

/-- The functions the analysis skips have no postcondition. -/
theorem skip_names : ((vsIdx :: guestXIdx).all fun j =>
    !postNames.contains (Data.coreFunctions.getD j default).name) = true := by
  decide +kernel
" ++ closing

/-- `l` assembled from runs, as `Guest.lean` takes it. -/
def tabOk (F : Fam) (stmt : String) (runs : List Run) (len : Nat) : String :=
  s!"theorem {F.tab}_ok : ∀ e ∈ {F.tab}, {stmt} = true := by
  have h : ({F.tab}.drop {len}).all (fun e => {F.check}) = true := all_end (by decide)
" ++ String.join (runs.reverse.map fun (s, n) =>
    s!"  have h := all_step {F.thm}_{s} (rfl : {s} + {n} = {s + n}) h\n") ++
  "  rw [List.drop_zero] at h\n  exact List.all_eq_true.mp h\n"

def chkAll (count : Nat) (runs : List Run) : String := Id.run do
  let rs := runs.reverse
  let (s0, n0) := rs.head!
  let mut out := s!"/-- **The analysis accepts every guest function it does not skip**, assembled. -/
theorem guest_chk_all : (List.range' 0 {count}).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  have h := evalE_{s0}\n"
  let mut acc := n0
  for (s, n) in rs.tail do
    out := out ++ s!"  have h := range_step evalE_{s} (rfl : {s} + {n} = {s + n}) h (rfl : {n} + {acc} = {n + acc})\n"
    acc := n + acc
  return out ++ "  exact h\n"

def allModule (mods : List String) (count : Nat) (eRuns : List Run) (T : Tables)
    (mainRuns loopRuns lqRuns' osRuns : List Run) : String :=
  "/-
  LeanVM.Guest.Compiled.Obl.Eval.All

  Generated by `lake exe guest-oblgen` (lean_vm/cli/GuestOblGen.lean); do not edit.
  The evaluations of `Eval/` put together: the analysis over every guest function it does not skip,
  and each `ext` family's check over its whole table.
-/

module

public import LeanVM.Compiler.Sound.Obl.Steps
" ++ String.join (mods.map fun m => s!"public import LeanVM.Guest.Compiled.Obl.Eval.{m}\n") ++
  opening ++ "\n" ++ chkAll count eRuns ++ "\n" ++
  tabOk mainFam "mainOk e.1 e.2.1 e.2.2.1 e.2.2.2" mainRuns T.mains.length ++ "\n" ++
  tabOk loopFam "loopOk e.1 e.2.1 e.2.2.1 e.2.2.2" loopRuns T.loops.length ++
  "\nset_option maxRecDepth 4000 in\n" ++
  tabOk lqFam "lqOk e.1 e.2.1 e.2.2" lqRuns' T.lqs.length ++ "\n" ++
  tabOk osFam "osOk e.1 e.2" osRuns T.os.length ++ closing

/-- Declaration `decl` replaced in `text`: its lines from the one starting with `start` to the
blank line after it. -/
def replaceDecl (file : String) (text start decl : String) : Except String String := do
  let ls := text.splitOn "\n"
  match (List.range ls.length).filter (fun i => (ls.getD i "").startsWith start) with
  | [i] =>
    let j := ((List.range ls.length).find? fun j => i < j && ls.getD j "" == "").getD ls.length
    let declLines := decl.splitOn "\n"
    let declLines := if declLines.getLast? == some "" then declLines.dropLast else declLines
    return "\n".intercalate (ls.take i ++ declLines ++ ls.drop j)
  | is => throw s!"{file}: {is.length} lines start with `{start}`, not one"

/-- The keys of `guestTab` in `GuestTab.lean`: names, and stable names under `name%`. -/
def guestTabKeys (text : String) : List String × List String := Id.run do
  let ls := text.splitOn "\n"
  let some i := ls.findIdx? (·.startsWith "def guestTab : Tab where") | return ([], [])
  let block := (ls.drop i).takeWhile (!·.startsWith "  pows :=")
  let mut names := []
  let mut stables := []
  for l in block do
    match l.splitOn "(\"" with
    | _ :: rest :: _ => names := names ++ [(rest.splitOn "\"").headD ""]
    | _ => match l.splitOn "(name% «" with
      | _ :: rest :: _ => stables := stables ++ [(rest.splitOn "»").headD ""]
      | _ => pure ()
  return (names, stables)

/-! ## Main -/

set_option compiler.extract_closed false in
def run (check : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanVM.Guest.CoreData },
    { module := `LeanVM.Guest.B1.Opening.Interface }] {} 0 (loadExts := false)
  let G ← IO.ofExcept (readGuest env)
  let count := G.fns.size
  let stableSet : Std.HashSet String := G.stable.foldl (init := {}) (·.insert ·)
  let nameSet : Std.HashSet String := G.fns.foldl (init := {}) fun s f => s.insert f.name
  -- the hand-written facts' functions, `guestTab`'s keys among them
  let mut missing : Array String := #[]
  for (s, what) in handFacts do
    unless stableSet.contains s do missing := missing.push s!"no core function {s}: {what}"
  let tabPath := oblDir / "GuestTab.lean"
  let tabText ← IO.FS.readFile tabPath
  let (keys, stableKeys) := guestTabKeys tabText
  if keys.isEmpty then missing := missing.push s!"{tabPath}: no `guestTab`"
  for k in keys do
    unless nameSet.contains k do
      missing := missing.push s!"no core function {k}: its entry of `guestTab`"
  for k in stableKeys do
    unless stableSet.contains k do
      missing := missing.push s!"no core function of stable name {k}: its entry of `guestTab`"
  for k in postNames do
    unless stableSet.contains k do
      missing := missing.push s!"no core function {k}: `postNames` (Eval/Misc)"
  for pre in tabFamilies do
    for f in G.fns do
      if f.name.startsWith pre && !keys.contains f.name then
        missing := missing.push s!"{f.name}: no entry in `guestTab`, as every `{pre}…` has"
  unless missing.isEmpty do
    for m in missing do IO.eprintln s!"guest-oblgen: {m}"
    return 1
  let T ← IO.ofExcept (tables G)
  -- the runs of `Eval/E{kk}`
  let stableIdx : Std.HashMap String Nat :=
    (List.range G.stable.size).foldl (init := {}) fun m j => m.insert G.stable[j]! j
  let mut mods : List (List Nat) := []
  for ms in anchors do
    let mut starts := []
    for a in ms do
      match stableIdx[a]? with
      | some j => starts := starts ++ [j]
      | none =>
        IO.eprintln s!"guest-oblgen: anchor {a} is gone: its run is merged into the one before"
    unless starts.isEmpty do mods := mods ++ [starts]
  let flat := mods.flatten
  unless flat.head? == some 0 && (flat.zip flat.tail).all (fun (a, b) => a < b) &&
      flat.getLast! < count do
    IO.eprintln s!"guest-oblgen: the anchors are not in the guest's order from `main`: {flat}"
    return 1
  let ends := flat.tail ++ [count]
  let eRuns : List Run := (flat.zip ends).map fun (a, b) => (a, b - a)
  let mut files : Array (System.FilePath × String) := #[]
  let mut k := 0
  let mut eNames := []
  for ms in mods do
    let runs := eRuns.filter fun r => ms.contains r.1
    let (a, _) := runs.head!
    let (s, n) := runs.getLast!
    let m := s!"E{if k < 10 then "0" else ""}{k}"
    files := files.push (evalDir / s!"{m}.lean", eModule k a (s + n - 1) runs)
    eNames := eNames ++ [m]
    k := k + 1
  -- the families
  let nM := T.mains.length
  let nL := T.loops.length
  let hL := (nL + 1) / 2
  let nQ := T.lqs.length
  let nO := T.os.length
  let hO := (nO + 1) / 2
  let mainRuns := runsOf 0 nM mainRun
  let loopRuns0 := runsOf 0 hL loopRun
  let loopRuns1 := runsOf hL nL loopRun
  let lqRuns' := runsOf 0 nQ ((nQ + lqRuns - 1) / lqRuns)
  let osRuns0 := runsOf 0 hO osRun
  let osRuns1 := runsOf hO nO osRun
  let osName (i : Nat) : String := (T.os.getD i (0, "", [])).2.1
  let osRange (a b : Nat) : String :=
    s!"`{osName a}` to `{(osName b).drop "open_stacked".length}` pass `osOk`, by kernel evaluation."
  files := files ++ #[
    (evalDir / "XMain.lean", xModule "XMain"
      "The `opening_queries` specializations pass `mainOk`, by kernel evaluation." "Walk" mainFam
      mainRuns),
    (evalDir / "XLoop0.lean", xModule "XLoop0"
      "The loop helpers of `opening_queries` pass `loopOk` (first half), by kernel evaluation." "Walk"
      loopFam loopRuns0),
    (evalDir / "XLoop1.lean", xModule "XLoop1"
      "The loop helpers of `opening_queries` pass `loopOk` (second half), by kernel evaluation." "Walk"
      loopFam loopRuns1),
    (evalDir / "XLq.lean", xModule "XLq"
      "The `level_queries` specializations pass `lqOk`, by kernel evaluation." "Lq" lqFam lqRuns'),
    (evalDir / "XOs0.lean", xModule "XOs0" (osRange 0 (hO - 1)) "Os" osFam osRuns0),
    (evalDir / "XOs1.lean", xModule "XOs1" (osRange hO (nO - 1)) "Os" osFam osRuns1)]
  let vsFn := G.fns[T.vs]!
  unless vsFn.params.all fun v => v == V.n v.idx do
    IO.eprintln "guest-oblgen: verify_sub's parameters are not `.n i`"
    return 1
  let vsParams := s!"[{", ".intercalate (vsFn.params.map fun v => s!".n {v.idx}")}]"
  files := files.push (evalDir / "Misc.lean", misc count vsParams)
  let allMods := eNames ++ ["Misc", "XMain", "XLoop0", "XLoop1", "XLq", "XOs0", "XOs1"]
  files := files.push (evalDir / "All.lean",
    allModule allMods count eRuns T mainRuns (loopRuns0 ++ loopRuns1) lqRuns' (osRuns0 ++ osRuns1))
  files := files.push (oblDir / "GuestXTab.lean", guestXTab T)
  let xPath := oblDir / "GuestX.lean"
  let xText ← IO.FS.readFile xPath
  files := files.push (xPath,
    ← IO.ofExcept (replaceDecl xPath.toString xText "def xTab :" (xTabDecl T)))
  let tab ← IO.ofExcept (replaceDecl tabPath.toString tabText "def guestXIdx :" (guestXIdxDecl T))
  files := files.push (tabPath,
    ← IO.ofExcept (replaceDecl tabPath.toString tab "def vsIdx :" (vsIdxDecl T)))
  -- write or compare; `Eval/` holds the files written here only
  let written := files.map (·.1)
  let mut stale : Array String := #[]
  for (p, t) in files do
    let old ← if ← p.pathExists then IO.FS.readFile p else pure ""
    if old != t then
      stale := stale.push s!"{if check then "stale" else "wrote"} {p}"
      unless check do IO.FS.writeFile p t
  for e in ← evalDir.readDir do
    if e.path.extension == some "lean" && !written.contains e.path then
      stale := stale.push s!"{if check then "not written here" else "removed"} {e.path}"
      unless check do IO.FS.removeFile e.path
  IO.println s!"guest-oblgen: {count} functions, {eRuns.length} runs in {eNames.length} modules, \
    {T.xIdx.length} ext functions ({nM} opening_queries, {nL} loop helpers, {nQ} level_queries, \
    {nO} open_stacked)"
  for s in stale do IO.println s!"guest-oblgen: {s}"
  if stale.isEmpty then IO.println "guest-oblgen: every file is current"
  return if check && !stale.isEmpty then 1 else 0

end GuestOblGen

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => GuestOblGen.run false
  | ["--check"] => GuestOblGen.run true
  | _ =>
    IO.eprintln "usage: lake exe guest-oblgen [--check]"
    return 2
